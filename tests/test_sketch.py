import json
import unittest
from contextlib import ExitStack
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

import sketch_runner
from glm_client import GLMClientError
from sketch_runner import (
    AUDIT_REJECTED,
    BUDGET_EXHAUSTED,
    HOLE_FAILED,
    REJECTED,
    SKETCH_FORMAT_ERROR,
    TIMEOUT,
    VERIFIER_ERROR,
    parse_sketch,
    run_sketch,
)


class FakeClient:
    def __init__(self, outputs):
        self.outputs = iter(outputs)
        self.prompts = []

    def generate(self, prompt, *, max_tokens=None):
        self.prompts.append(prompt)
        item = next(self.outputs)
        if isinstance(item, Exception):
            raise item
        return item


class SketchTests(unittest.TestCase):
    def task(self, **extra):
        value = {
            "id": "test_sketch",
            "prompt": "Prove the trivial goal.",
            "template_path": "template.dfy",
            "allowed_holes": ["A", "B"],
            "min_holes": 2,
            "max_holes": 2,
            "max_sketch_rounds": 1,
            "max_hole_rounds": 1,
            "max_calls": 3,
            "timeout_seconds": 30,
        }
        value.update(extra)
        return value

    @staticmethod
    def _clean_audit(source, *, timeout_seconds):
        return sketch_runner.VerificationResult("VERIFIED", True, "audit clean")

    def _patch_dafny(self, verify, audit=None):
        """Patch both Dafny entry points; stage 3 audits without re-verifying."""
        stack = ExitStack()
        stack.enter_context(
            patch.object(sketch_runner, "verify_dafny_source", side_effect=verify)
        )
        stack.enter_context(
            patch.object(
                sketch_runner, "audit_dafny_source", side_effect=audit or self._clean_audit
            )
        )
        return stack

    def test_parse_orders_and_deduplicates_holes(self):
        sketch, holes, error = parse_sketch(
            "lemma A(n: nat) ensures n >= 0 { HOLE_A HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }\n"
            "",
            self.task(),
        )
        self.assertIsNone(error)
        self.assertIsNotNone(sketch)
        self.assertEqual(holes, ["A", "B"])

    def test_parse_rejects_unknown_or_trust_escape(self):
        sketch, _, error = parse_sketch(
            "lemma A(n: nat) ensures n >= 0 { assume false; HOLE_A }\n"
            "lemma C(n: nat) ensures n >= 0 { HOLE_C }",
            self.task(min_holes=1, max_holes=3),
        )
        self.assertIsNone(sketch)
        self.assertEqual(error, "sketch contains a forbidden declaration or trust escape")

    def test_parse_accepts_holes_inside_nested_blocks(self):
        """A brace-matched body keeps nested blocks, which a flat regex cut short."""
        sketch, holes, error = parse_sketch(
            "lemma A(n: nat) ensures n >= 0 {\n"
            "  if n == 0 { HOLE_A } else { forall k | k < n { HOLE_B } }\n"
            "}",
            self.task(),
        )
        self.assertIsNone(error)
        self.assertIsNotNone(sketch)
        self.assertEqual(holes, ["A", "B"])

    def test_parse_ignores_braces_inside_literals(self):
        sketch, holes, error = parse_sketch(
            'lemma A(n: nat) ensures n >= 0 { assert "}" != "{"; HOLE_A }\n'
            "lemma B(n: nat) ensures n >= 0 { var c := '}'; HOLE_B }",
            self.task(),
        )
        self.assertIsNone(error)
        self.assertIsNotNone(sketch)
        self.assertEqual(holes, ["A", "B"])

    def test_parse_keeps_identifier_prime_out_of_char_literals(self):
        sketch, holes, error = parse_sketch(
            "lemma A(n: nat) ensures n >= 0 { var n' := n; HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
            self.task(),
        )
        self.assertIsNone(error)
        self.assertIsNotNone(sketch)
        self.assertEqual(holes, ["A", "B"])

    def test_parse_rejects_a_lemma_without_a_body(self):
        """A bodyless lemma is an assumption, even when its signature ends in a set."""
        for declaration in (
            "lemma A(n: nat) ensures n >= 0",
            "lemma A(n: nat) ensures n in {0, 1}",
        ):
            with self.subTest(declaration=declaration):
                sketch, _, error = parse_sketch(
                    declaration + "\nlemma B(n: nat) ensures n >= 0 { HOLE_A HOLE_B }",
                    self.task(),
                )
                self.assertIsNone(sketch)
                self.assertEqual(error, "every lemma must have a proof body")

    def test_parse_accepts_a_set_literal_before_the_body(self):
        sketch, holes, error = parse_sketch(
            "lemma A(n: nat) ensures n in {0, 1} || n >= 0 { HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
            self.task(),
        )
        self.assertIsNone(error)
        self.assertIsNotNone(sketch)
        self.assertEqual(holes, ["A", "B"])

    def test_parse_rejects_unbalanced_braces(self):
        sketch, _, error = parse_sketch(
            "lemma A(n: nat) ensures n >= 0 { if n == 0 { HOLE_A }",
            self.task(min_holes=1, max_holes=1),
        )
        self.assertIsNone(sketch)
        self.assertEqual(error, "sketch has an unbalanced opening brace")

    def test_two_hole_flow_requires_all_verified(self):
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text(
                "{{SKETCH}}\nlemma RequiredGoal(n: nat) ensures true { }\n",
                encoding="utf-8",
            )
            result = run_sketch(
                FakeClient([
                    "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                    "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
                    "assert n >= 0;",
                    "assert n >= 0;",
                ]),
                self.task(),
                project_dir=project,
            )
        self.assertTrue(result["success"])
        self.assertEqual(result["final_status"], "VERIFIED")
        self.assertEqual([h["status"] for h in result["holes"]], ["VERIFIED", "VERIFIED"])

    def test_failed_hole_never_reports_success(self):
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            result = run_sketch(
                FakeClient([
                    "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                    "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
                    "assert n < 0;",
                    "assert n < 0;",
                ]),
                self.task(),
                project_dir=project,
            )
        self.assertFalse(result["success"])
        self.assertEqual(result["final_status"], HOLE_FAILED)

    def test_hole_retry_prompt_contains_complete_previous_diagnostics(self):
        """A failed hole retry receives its complete, structured verifier result."""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = FakeClient([
                "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
                "assert bad_candidate;",
                "assert n >= 0;",
                "assert n >= 0;",
            ])
            calls = []

            def verify(source, *, timeout_seconds, audit):
                calls.append((source, audit))
                if len(calls) == 1:  # sketch with internal stubs
                    return sketch_runner.VerificationResult("VERIFIED", True, "sketch ok")
                if "bad_candidate" in source:
                    return sketch_runner.VerificationResult(
                        "REJECTED",
                        False,
                        "first diagnostic line\nsecond diagnostic line\nthird diagnostic line",
                        counterexample={"n": -7, "expected": 7},
                    )
                return sketch_runner.VerificationResult("VERIFIED", True, "ok")

            task = self.task(max_hole_rounds=2, max_calls=6)
            with self._patch_dafny(verify):
                result = run_sketch(client, task, project_dir=project)

        self.assertTrue(result["success"])
        # Prompt 0 is sketch, prompt 1 is A's first attempt, prompt 2 is A's retry.
        retry_prompt = client.prompts[2]
        self.assertIn("Prove the trivial goal.", retry_prompt)
        self.assertIn("Fill only the Dafny proof body for hole A", retry_prompt)
        self.assertIn("lemma A(n: nat) ensures n >= 0 { HOLE_A }", retry_prompt)
        self.assertIn("assert bad_candidate;", retry_prompt)
        self.assertIn("REJECTED", retry_prompt)
        self.assertIn("first diagnostic line", retry_prompt)
        self.assertIn("second diagnostic line", retry_prompt)
        self.assertIn("third diagnostic line", retry_prompt)
        self.assertIn("-7", retry_prompt)
        self.assertIn("expected", retry_prompt)
        # A new hole starts with a clean diagnostic context, while retaining the sketch.
        next_hole_prompt = client.prompts[3]
        self.assertIn("Fill only the Dafny proof body for hole B", next_hole_prompt)
        self.assertIn("lemma A(n: nat) ensures n >= 0 { HOLE_A }", next_hole_prompt)
        self.assertNotIn("first diagnostic line", next_hole_prompt)
        self.assertNotIn("second diagnostic line", next_hole_prompt)
        self.assertNotIn("third diagnostic line", next_hole_prompt)
        self.assertNotIn("bad_candidate", next_hole_prompt)

    def test_hole_diagnostics_are_scoped_and_latest_attempt_wins(self):
        """Retries use only the immediately preceding failure for the same hole."""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = FakeClient([
                "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
                "assert candidate_one;",
                "assert candidate_two;",
                "assert candidate_three;",
            ])
            calls = []

            def verify(source, *, timeout_seconds, audit):
                calls.append(source)
                if len(calls) == 1:
                    return sketch_runner.VerificationResult("VERIFIED", True, "sketch ok")
                if "candidate_one" in source:
                    return sketch_runner.VerificationResult("REJECTED", False, "diagnostic one")
                if "candidate_two" in source:
                    return sketch_runner.VerificationResult("REJECTED", False, "diagnostic two")
                return sketch_runner.VerificationResult("REJECTED", False, "diagnostic three")

            task = self.task(max_hole_rounds=3, max_calls=5)
            with patch.object(sketch_runner, "verify_dafny_source", side_effect=verify):
                result = run_sketch(client, task, project_dir=project)

        self.assertFalse(result["success"])
        self.assertEqual(result["final_status"], HOLE_FAILED)
        retry_two = client.prompts[2]
        retry_three = client.prompts[3]
        self.assertIn("diagnostic one", retry_two)
        self.assertNotIn("diagnostic two", retry_two)
        self.assertIn("diagnostic two", retry_three)
        self.assertNotIn("diagnostic one", retry_three)
        self.assertNotIn("diagnostic three", retry_three)

    def test_format_error_retry_has_no_stale_candidate(self):
        """A malformed response carries its format error, without an old candidate."""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = FakeClient([
                "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
                "assert stale_candidate;",
                "",  # format error; the earlier candidate must not leak into the next prompt
                "assert n >= 0;",
                "assert n >= 0;",
            ])
            calls = []

            def verify(source, *, timeout_seconds, audit):
                calls.append(source)
                if "stale_candidate" in source:
                    return sketch_runner.VerificationResult("REJECTED", False, "candidate rejected")
                return sketch_runner.VerificationResult("VERIFIED", True, "ok")

            task = self.task(max_hole_rounds=3, max_calls=7)
            with self._patch_dafny(verify):
                result = run_sketch(client, task, project_dir=project)

        self.assertTrue(result["success"])
        retry_prompt = client.prompts[3]
        self.assertIn("FORMAT_ERROR", retry_prompt)
        self.assertNotIn("stale_candidate", retry_prompt)

    def test_parse_rejects_verification_scope_attributes(self):
        """{:verify false}、assert {:only} 等属性会跳过或缩小 Dafny 的检查范围。"""
        for sketch in (
            "lemma {:verify false} A(n: nat) ensures 1 == 2 { HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
            "lemma A(n: nat) ensures n >= 0 { assert {:only} n >= 0; HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
            "lemma {:timeLimit 9999} A(n: nat) ensures n >= 0 { HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
            "lemma {:rlimit 99999999} A(n: nat) ensures n >= 0 { HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
        ):
            with self.subTest(sketch=sketch.split("\n")[0]):
                parsed, _, error = parse_sketch(sketch, self.task())
                self.assertIsNone(parsed)
                self.assertEqual(
                    error, "sketch contains a forbidden declaration or trust escape"
                )

    def test_parse_keeps_harmless_attributes(self):
        """只封杀影响验证范围和开销的属性，{:induction} 之类必须继续可用。"""
        sketch, holes, error = parse_sketch(
            "lemma {:induction n} A(n: nat) ensures n >= 0 { HOLE_A }\n"
            "lemma {:trigger} B(n: nat) ensures n >= 0 { HOLE_B }",
            self.task(),
        )
        self.assertIsNone(error)
        self.assertIsNotNone(sketch)
        self.assertEqual(holes, ["A", "B"])

    def test_fill_does_not_corrupt_a_longer_hole_name(self):
        """HOLE_A must not eat the prefix of HOLE_AB, whatever the fill order."""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            task = self.task(allowed_holes=["A", "AB"])
            sketch = "lemma X(n: nat) ensures n >= 0 { HOLE_A HOLE_AB }"
            rendered = sketch_runner.assemble_sketch(
                task,
                project,
                sketch,
                {"A": "assert n >= 0;", "AB": "assert n + 1 > 0;"},
                internal_stubs=False,
            )
        self.assertIn("assert n >= 0; assert n + 1 > 0;", rendered)
        self.assertNotIn("HOLE_", rendered)

    def test_fill_keeps_a_backslash_in_the_body(self):
        """re.sub must not read the model's body as a replacement template."""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            rendered = sketch_runner.assemble_sketch(
                self.task(min_holes=1, max_holes=1),
                project,
                "lemma A(n: nat) ensures n >= 0 { HOLE_A }",
                {"A": r'assert "a\\b" != "";'},
                internal_stubs=False,
            )
        self.assertIn(r'assert "a\\b" != "";', rendered)

    def test_unverifiable_sketch_is_not_reported_as_a_parse_error(self):
        """A sketch that parses but never verifies is REJECTED, not FORMAT_ERROR."""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = FakeClient([
                "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
                "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
            ])

            def verify(source, *, timeout_seconds, audit):
                return sketch_runner.VerificationResult(
                    REJECTED, False, "postcondition might not hold"
                )

            task = self.task(max_sketch_rounds=2, max_calls=4)
            with patch.object(sketch_runner, "verify_dafny_source", side_effect=verify):
                result = run_sketch(client, task, project_dir=project)

        self.assertFalse(result["success"])
        self.assertEqual(result["final_status"], REJECTED)
        self.assertEqual([r["status"] for r in result["sketch_rounds"]], [REJECTED, REJECTED])

    def test_unparseable_sketch_still_reports_a_parse_error(self):
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            #第一轮能解析但被拒，第二轮连解析都没过：最终状态跟随最后一轮
            client = FakeClient([
                "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
                "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
                "there is no Dafny here",
            ])

            def verify(source, *, timeout_seconds, audit):
                return sketch_runner.VerificationResult(REJECTED, False, "rejected")

            task = self.task(max_sketch_rounds=2, max_calls=4)
            with patch.object(sketch_runner, "verify_dafny_source", side_effect=verify):
                result = run_sketch(client, task, project_dir=project)

        self.assertEqual(result["final_status"], SKETCH_FORMAT_ERROR)

    def _sketch_client(self, *tail):
        return FakeClient([
            "lemma A(n: nat) ensures n >= 0 { HOLE_A }\n"
            "lemma B(n: nat) ensures n >= 0 { HOLE_B }",
            *tail,
        ])

    def test_api_error_records_the_unfinished_hole(self):
        """An aborted hole is still reported, so the failure point stays visible."""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = self._sketch_client(GLMClientError("safe failure"))

            def verify(source, *, timeout_seconds, audit):
                return sketch_runner.VerificationResult("VERIFIED", True, "ok")

            with patch.object(sketch_runner, "verify_dafny_source", side_effect=verify):
                result = run_sketch(client, self.task(), project_dir=project)

        self.assertFalse(result["success"])
        self.assertEqual(result["final_status"], "API_ERROR")
        self.assertEqual(len(result["holes"]), 1)
        self.assertEqual(result["holes"][0]["name"], "A")
        self.assertEqual(result["holes"][0]["status"], "API_ERROR")
        self.assertEqual(result["holes"][0]["rounds"], 0)
        self.assertEqual(result["holes"][0]["attempts"], [])

    def test_call_budget_is_not_reported_as_an_api_error(self):
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = self._sketch_client("assert n >= 0;")

            def verify(source, *, timeout_seconds, audit):
                return sketch_runner.VerificationResult("VERIFIED", True, "ok")

            #预算只够草图和 hole A，hole B 一开口就被拦下
            task = self.task(max_calls=2)
            with patch.object(sketch_runner, "verify_dafny_source", side_effect=verify):
                result = run_sketch(client, task, project_dir=project)

        self.assertEqual(result["final_status"], BUDGET_EXHAUSTED)
        self.assertEqual([h["status"] for h in result["holes"]], ["VERIFIED", BUDGET_EXHAUSTED])

    def test_total_timeout_shrinks_each_dafny_call(self):
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = self._sketch_client("assert n >= 0;", "assert n >= 0;")
            budgets = []

            def verify(source, *, timeout_seconds, audit):
                budgets.append(timeout_seconds)
                return sketch_runner.VerificationResult("VERIFIED", True, "ok")

            def audit(source, *, timeout_seconds):
                budgets.append(timeout_seconds)
                return sketch_runner.VerificationResult("VERIFIED", True, "audit clean")

            task = self.task(timeout_seconds=600, total_timeout_seconds=5, max_calls=6)
            with self._patch_dafny(verify, audit):
                result = run_sketch(client, task, project_dir=project)

        self.assertTrue(result["success"])
        self.assertTrue(budgets)
        for budget in budgets:
            self.assertGreaterEqual(budget, 1)
            self.assertLessEqual(budget, 5)

    def test_final_stage_verifies_once_and_audits_once(self):
        """最终阶段只跑一次 verify 和一次 audit，不再由 audit 内部重验一遍。"""
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = self._sketch_client("assert n >= 0;", "assert n >= 0;")
            verifies, audits = [], []

            def verify(source, *, timeout_seconds, audit):
                verifies.append(audit)
                return sketch_runner.VerificationResult("VERIFIED", True, "ok")

            def audit(source, *, timeout_seconds):
                audits.append(source)
                return sketch_runner.VerificationResult("VERIFIED", True, "audit clean")

            with self._patch_dafny(verify, audit):
                result = run_sketch(client, self.task(max_calls=6), project_dir=project)

        self.assertTrue(result["success"])
        #草图 1 次 + 两个 hole 各 1 次 + 最终 1 次 = 4 次 verify，且都不带 audit
        self.assertEqual(verifies, [False, False, False, False])
        self.assertEqual(len(audits), 1)
        self.assertEqual(result["final_audit"]["status"], "VERIFIED")

    def _timed_run(self, spent, total_timeout_seconds):
        """Run with a controllable clock that the sketch-stage verify advances.

        Sleeping against a 1 s budget raced with the 15.6 ms resolution of
        ``time.monotonic`` on Windows: whether the budget ran out during the
        sketch stage or the hole stage depended on whether the clock had ticked
        yet.  Driving the clock by hand pins the path being tested.
        """
        clock = [0.0]
        verifies = []

        def verify(source, *, timeout_seconds, audit):
            verifies.append(timeout_seconds)
            clock[0] += spent#这一次 Dafny 调用花掉的时间
            return sketch_runner.VerificationResult("VERIFIED", True, "ok")

        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = self._sketch_client("assert n >= 0;")
            task = self.task(total_timeout_seconds=total_timeout_seconds)
            with patch.object(sketch_runner.time, "monotonic", lambda: clock[0]), \
                 self._patch_dafny(verify):
                return run_sketch(client, task, project_dir=project), verifies

    def test_exhausted_time_budget_records_the_aborted_hole(self):
        """总预算在草图阶段用光：hole 阶段一开口就被拦下，但仍留下记录。"""
        result, verifies = self._timed_run(spent=2.5, total_timeout_seconds=2)
        self.assertFalse(result["success"])
        self.assertEqual(result["final_status"], TIMEOUT)
        self.assertEqual([h["status"] for h in result["holes"]], [TIMEOUT])
        self.assertEqual(len(verifies), 1)#没有再启动新的 Dafny 调用

    def test_no_dafny_call_starts_with_under_a_second_left(self):
        """剩余不足 1 秒：模型还能问，但不再启动新的验证。"""
        result, verifies = self._timed_run(spent=1.5, total_timeout_seconds=2)
        self.assertEqual(result["final_status"], TIMEOUT)
        self.assertEqual([h["status"] for h in result["holes"]], [TIMEOUT])
        self.assertEqual(verifies, [2])#草图那次拿到 2 秒，hole 那次没发生

    def _run_to_final_stage(self, final_verify, final_audit):
        """Drive both holes to VERIFIED, then control the two closing calls."""
        results = iter([
            sketch_runner.VerificationResult("VERIFIED", True, "sketch ok"),
            sketch_runner.VerificationResult("VERIFIED", True, "hole A ok"),
            sketch_runner.VerificationResult("VERIFIED", True, "hole B ok"),
            final_verify,
        ])
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = self._sketch_client("assert n >= 0;", "assert n >= 0;")

            def verify(source, *, timeout_seconds, audit):
                return next(results)

            def audit(source, *, timeout_seconds):
                return final_audit

            with self._patch_dafny(verify, audit):
                return run_sketch(client, self.task(max_calls=6), project_dir=project)

    def test_final_stage_reports_the_underlying_cause(self):
        """A timeout or verifier fault must not be relabelled as a stage verdict."""
        verified = sketch_runner.VerificationResult("VERIFIED", True, "final ok")
        cases = [
            (sketch_runner.VerificationResult(TIMEOUT, False, "verify timed out"), verified, TIMEOUT),
            (sketch_runner.VerificationResult(VERIFIER_ERROR, False, "dafny missing"), verified, VERIFIER_ERROR),
            (sketch_runner.VerificationResult("REJECTED", False, "not provable"), verified, "ASSEMBLY_ERROR"),
            (verified, sketch_runner.VerificationResult(TIMEOUT, False, "audit timed out"), TIMEOUT),
            (verified, sketch_runner.VerificationResult("REJECTED", False, "1 finding"), AUDIT_REJECTED),
        ]
        for final_verify, final_audit, expected in cases:
            with self.subTest(expected=expected):
                result = self._run_to_final_stage(final_verify, final_audit)
                self.assertFalse(result["success"])
                self.assertEqual(result["final_status"], expected)

    def test_verifier_error_in_a_hole_stops_immediately(self):
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text("{{SKETCH}}", encoding="utf-8")
            client = self._sketch_client("assert n >= 0;", "assert n >= 0;", "assert n >= 0;")
            calls = []

            def verify(source, *, timeout_seconds, audit):
                calls.append(source)
                if len(calls) == 1:
                    return sketch_runner.VerificationResult("VERIFIED", True, "sketch ok")
                return sketch_runner.VerificationResult(VERIFIER_ERROR, False, "dafny missing")

            task = self.task(max_hole_rounds=3, max_calls=6)
            with patch.object(sketch_runner, "verify_dafny_source", side_effect=verify):
                result = run_sketch(client, task, project_dir=project)

        self.assertEqual(result["final_status"], VERIFIER_ERROR)
        self.assertEqual(result["holes"][0]["rounds"], 1)  # no retry against a broken verifier


class NestedSketchTests(unittest.TestCase):
    """填 hole 时交回子草图：递归分解、命名与预算约束。"""

    ROOT = "lemma MainProof(n: nat) ensures n >= 0 { HOLE_Main }"
    #体在前、新引理在后
    EXPANSION = (
        "if n == 0 { } else { Step(n); }\n"
        "lemma Step(n: nat) ensures n >= 0 { HOLE_Main_step }"
    )

    def task(self, **extra):
        value = {
            "id": "nested",
            "prompt": "Prove the goal.",
            "template_path": "template.dfy",
            "allowed_holes": ["Main"],
            "min_holes": 1,
            "max_holes": 1,
            "max_hole_depth": 3,
            "max_child_holes": 4,
            "max_total_holes": 12,
            "max_sketch_rounds": 1,
            "max_hole_rounds": 2,
            "max_calls": 8,
            "timeout_seconds": 30,
        }
        value.update(extra)
        return value

    def _expand(self, body, declarations, **extra):
        """Run plan_expansion with permissive defaults, overriding one axis."""
        options = {
            "depth": 1,
            "max_depth": 3,
            "max_children": 4,
            "room": 12,
            "used_holes": {"Main"},
            "used_lemmas": {"MainProof", "RequiredGoal"},
        }
        options.update(extra)
        return sketch_runner.plan_expansion("Main", body, declarations, **options)

    def test_split_separates_body_from_new_declarations(self):
        body, declarations, error = sketch_runner.split_hole_response(self.EXPANSION)
        self.assertIsNone(error)
        self.assertEqual(body, "if n == 0 { } else { Step(n); }")
        self.assertTrue(declarations.startswith("lemma Step"))

    def test_split_treats_a_plain_body_as_a_leaf(self):
        body, declarations, error = sketch_runner.split_hole_response(
            "if n == 0 { } else { MainProof(n - 1); }"
        )
        self.assertIsNone(error)
        self.assertEqual(declarations, "")
        self.assertIn("MainProof(n - 1)", body)

    def test_declarations_written_before_the_body_are_rejected(self):
        body, declarations, error = sketch_runner.split_hole_response(
            "lemma Step(n: nat) ensures n >= 0 { HOLE_Main_step }\nassert n >= 0;"
        )
        self.assertIsNone(error)  # 切分本身成功，问题由展开校验报出
        self.assertEqual(body, "")  # 第一个 lemma 之前什么都没有
        children, plan_error = self._expand(body, declarations)
        self.assertEqual(children, [])
        #顺序写反时，先撞上"这个洞自己的证明体在哪"，这正是模型要改的地方
        self.assertIn("needs its own proof body", plan_error)

    def test_expansion_accepts_a_well_formed_sub_sketch(self):
        body, declarations, _ = sketch_runner.split_hole_response(self.EXPANSION)
        children, error = self._expand(body, declarations)
        self.assertIsNone(error)
        self.assertEqual(children, ["Main_step"])

    def test_child_hole_must_carry_the_parent_prefix(self):
        _, error = self._expand(
            "Step(n);", "lemma Step(n: nat) ensures n >= 0 { HOLE_Other }"
        )
        self.assertIn("HOLE_Main_<suffix>", error)
        self.assertIn("Other", error)

    def test_child_hole_may_not_reuse_a_name(self):
        _, error = self._expand(
            "Step(n);",
            "lemma Step(n: nat) ensures n >= 0 { HOLE_Main_a }",
            used_holes={"Main", "Main_a"},
        )
        self.assertIn("already in use", error)

    def test_expansion_may_not_redeclare_an_existing_lemma(self):
        _, error = self._expand(
            "RequiredGoal(n);",
            "lemma RequiredGoal(n: nat) ensures n >= 0 { HOLE_Main_a }",
        )
        self.assertIn("already declared", error)

    def test_expansion_needs_its_own_body(self):
        _, error = self._expand(
            "", "lemma Step(n: nat) ensures n >= 0 { HOLE_Main_step }"
        )
        self.assertIn("needs its own proof body", error)

    def test_expansion_respects_the_depth_limit(self):
        body, declarations, _ = sketch_runner.split_hole_response(self.EXPANSION)
        _, error = self._expand(body, declarations, depth=3, max_depth=3)
        self.assertIn("nesting depth 3 is exhausted", error)
        self.assertIn("no HOLE_ marker", error)

    def test_expansion_respects_the_breadth_and_total_limits(self):
        declarations = "\n".join(
            f"lemma S{i}(n: nat) ensures n >= 0 {{ HOLE_Main_{i} }}" for i in range(3)
        )
        _, error = self._expand("S0(n); S1(n); S2(n);", declarations, max_children=2)
        self.assertIn("at most 2 new holes", error)
        _, error = self._expand("S0(n); S1(n); S2(n);", declarations, room=1)
        self.assertIn("only grow by 1", error)

    def test_expansion_holes_must_sit_inside_lemma_bodies(self):
        _, error = self._expand(
            "Step(n);",
            "lemma Step(n: nat) requires HOLE_Main_a > 0 ensures n >= 0 { assert n >= 0; }",
        )
        self.assertEqual(error, "hole markers must occur inside lemma bodies")

    def _run(self, replies, verify, task=None):
        with TemporaryDirectory() as directory:
            project = Path(directory)
            (project / "template.dfy").write_text(
                "{{SKETCH}}\nlemma RequiredGoal(n: nat) ensures n >= 0 { MainProof(n); }\n",
                encoding="utf-8",
            )
            client = FakeClient(replies)
            with patch.object(sketch_runner, "verify_dafny_source", side_effect=verify), \
                 patch.object(
                     sketch_runner,
                     "audit_dafny_source",
                     side_effect=lambda source, *, timeout_seconds: (
                         sketch_runner.VerificationResult("VERIFIED", True, "audit clean")
                     ),
                 ):
                return client, run_sketch(client, task or self.task(), project_dir=project)

    @staticmethod
    def _accept(source, *, timeout_seconds, audit):
        return sketch_runner.VerificationResult("VERIFIED", True, "ok")

    def test_nested_run_records_the_hole_tree(self):
        client, result = self._run(
            [self.ROOT, self.EXPANSION, "assert n >= 0;"], self._accept
        )
        self.assertTrue(result["success"])
        tree = {h["name"]: h for h in result["holes"]}
        self.assertEqual(set(tree), {"Main", "Main_step"})
        self.assertEqual(tree["Main"]["kind"], "expanded")
        self.assertEqual(tree["Main"]["children"], ["Main_step"])
        self.assertEqual(tree["Main"]["depth"], 1)
        self.assertIsNone(tree["Main"]["parent"])
        self.assertEqual(tree["Main_step"]["kind"], "leaf")
        self.assertEqual(tree["Main_step"]["depth"], 2)
        self.assertEqual(tree["Main_step"]["parent"], "Main")
        self.assertIn("lemma Step", result["sketch"])
        self.assertNotIn("HOLE_", result["final_program"])
        self.assertNotIn("assume", result["final_program"])

    def test_depth_is_announced_in_the_hole_prompt(self):
        client, result = self._run(
            [self.ROOT, self.EXPANSION, "assert n >= 0;"], self._accept
        )
        self.assertTrue(result["success"])
        self.assertIn("nesting depth 1", client.prompts[1])#Main 可以继续分解
        self.assertIn("HOLE_Main_<suffix>", client.prompts[1])
        self.assertIn("nesting depth 2", client.prompts[2])#Main_step 也还能分解

    def test_flat_task_refuses_a_nested_answer(self):
        """max_hole_depth=1 时行为与嵌套功能加入前一致。"""
        client, result = self._run(
            [self.ROOT, self.EXPANSION, "assert n >= 0;"],
            self._accept,
            task=self.task(max_hole_depth=1, max_hole_rounds=2),
        )
        self.assertTrue(result["success"])#第二轮给出叶子体后成功
        main = result["holes"][0]
        self.assertEqual(main["kind"], "leaf")
        self.assertEqual(main["rounds"], 2)
        rejected = main["attempts"][0]["verification"]
        self.assertEqual(rejected["status"], "FORMAT_ERROR")
        self.assertIn("nesting depth 1 is exhausted", rejected["feedback"])
        self.assertIn("may not be decomposed", client.prompts[1])

    def test_a_rejected_expansion_does_not_pollute_the_sketch(self):
        bad = (
            "if n == 0 { } else { Broken(n); }\n"
            "lemma Broken(n: nat) ensures n >= 0 { HOLE_Main_bad }"
        )

        def verify(source, *, timeout_seconds, audit):
            if "Broken" in source:
                return sketch_runner.VerificationResult("REJECTED", False, "bad structure")
            return sketch_runner.VerificationResult("VERIFIED", True, "ok")

        client, result = self._run(
            [self.ROOT, bad, self.EXPANSION, "assert n >= 0;"],
            verify,
            task=self.task(max_hole_rounds=3, max_calls=8),
        )
        self.assertTrue(result["success"])
        self.assertNotIn("Broken", result["sketch"])#失败的展开没有留下声明
        self.assertNotIn("Main_bad", result["sketch"])
        tree = {h["name"]: h for h in result["holes"]}
        self.assertEqual(tree["Main"]["children"], ["Main_step"])
        self.assertEqual(tree["Main"]["rounds"], 2)

    def test_expansion_with_no_new_hole_is_terminal(self):
        """子引理当场证完也算一次合法展开，不会再排新的洞。"""
        client, result = self._run(
            [
                self.ROOT,
                "Step(n);\nlemma Step(n: nat) ensures n >= 0 { assert n >= 0; }",
            ],
            self._accept,
        )
        self.assertTrue(result["success"])
        self.assertEqual(len(result["holes"]), 1)
        self.assertEqual(result["holes"][0]["kind"], "expanded")
        self.assertEqual(result["holes"][0]["children"], [])

    def test_nested_sum_task_verifies_against_real_dafny(self):
        """真实 Dafny：根草图 -> 展开 -> 填子洞 -> 组装 -> audit 全程跑通。"""
        project = Path(__file__).resolve().parents[1]
        tasks = json.loads(
            (project / "tasks" / "formal_tasks.json").read_text(encoding="utf-8")
        )
        task = next(t for t in tasks if t["id"] == "dafny_sketch_sum_formula")
        client = FakeClient([
            "lemma MainProof(n: nat) ensures Sum(n) * 2 == n * (n + 1) { HOLE_Main }",
            "if n == 0 { } else { MainProof(n - 1); Step(n); }\n"
            "lemma Step(n: nat) requires n > 0 requires Sum(n - 1) * 2 == (n - 1) * n\n"
            "  ensures Sum(n) * 2 == n * (n + 1)\n"
            "{ HOLE_Main_step }",
            "assert Sum(n) == n + Sum(n - 1);",
        ])
        result = run_sketch(client, task, project_dir=project)
        self.assertEqual(result["final_status"], "VERIFIED")
        self.assertEqual(result["model_calls"], 3)
        self.assertEqual(
            [(h["name"], h["depth"], h["kind"]) for h in result["holes"]],
            [("Main", 1, "expanded"), ("Main_step", 2, "leaf")],
        )
        self.assertNotIn("HOLE_", result["final_program"])
        self.assertNotIn("assume", result["final_program"])
        self.assertEqual(result["final_audit"]["status"], "VERIFIED")


if __name__ == "__main__":
    unittest.main()
