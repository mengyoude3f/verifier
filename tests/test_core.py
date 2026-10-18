from __future__ import annotations

import importlib.util
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

import requests

from glm_client import (
    GLMClient,
    GLMConfig,
    GLMClientError,
    _extract_anthropic_text,
    _parse_key_file,
)
from runner import run_task
from screen_data import classify, screen
import verifiers
from verifiers import (
    REJECTED,
    TIMEOUT,
    UNKNOWN,
    VERIFIED,
    VERIFIER_ERROR,
    VerificationResult,
    audit_dafny_source,
    extract_candidate,
    verify_candidate,
    verify_z3_expression,
)

PROJECT_DIR = Path(__file__).resolve().parents[1]


class FakeClient:
    def __init__(self, outputs):
        self.outputs = iter(outputs)

    def generate(self, prompt: str, *, max_tokens=None) -> str:
        item = next(self.outputs)
        if isinstance(item, Exception):
            raise item
        return item


class FakeResponse:
    def __init__(self, status_code=200, *, payload=None, text=""):
        self.status_code = status_code
        self._payload = payload
        self.text = text
        self.ok = 200 <= status_code < 400

    def json(self):
        if isinstance(self._payload, Exception):
            raise self._payload
        if self._payload is None:
            raise ValueError("no JSON")
        return self._payload


class FakeSession:
    def __init__(self, outcomes):
        self.outcomes = iter(outcomes)
        self.calls = 0

    def post(self, *args, **kwargs):
        self.calls += 1
        outcome = next(self.outcomes)
        if isinstance(outcome, Exception):
            raise outcome
        return outcome


class CoreTests(unittest.TestCase):
    def test_anthropic_text_extraction(self):
        response = {
            "content": [
                {"type": "text", "text": "If(x >= 0, "},
                {"type": "text", "text": "x, -x)"},
            ]
        }
        self.assertEqual(_extract_anthropic_text(response), "If(x >= 0, x, -x)")

    def test_key_file_accepts_curl_authorization_header(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "api_key.md"
            path.write_text(
                'curl https://example.invalid/v1/messages -H '
                '"Authorization: Bearer test-placeholder"',
                encoding="utf-8",
            )
            self.assertEqual(_parse_key_file(path), "test-placeholder")

    def test_expression_extraction(self):
        candidate, error = extract_candidate(
            "```python\nIf(x >= 0, x, -x)\n```", "z3_expression"
        )
        self.assertIsNone(error)
        self.assertEqual(candidate, "If(x >= 0, x, -x)")

    @unittest.skipUnless(importlib.util.find_spec("z3"), "z3-solver is not installed")
    def test_z3_verifier(self):
        self.assertEqual(
            verify_z3_expression("abs", "If(x >= 0, x, -x)").status,
            VERIFIED,
        )
        self.assertEqual(verify_z3_expression("abs", "x").status, REJECTED)

    @unittest.skipUnless(importlib.util.find_spec("z3"), "z3-solver is not installed")
    def test_direct_and_feedback_modes(self):
        task = {
            "id": "test_abs",
            "name": "test abs",
            "verifier": "z3",
            "spec": "abs",
            "output_format": "z3_expression",
            "prompt": "return abs",
        }
        direct = run_task(
            FakeClient(["If(x >= 0, x, -x)"]),
            task,
            mode="direct",
            max_rounds=3,
            project_dir=PROJECT_DIR,
        )
        self.assertTrue(direct["success"])
        self.assertEqual(direct["rounds_used"], 1)

        repaired = run_task(
            FakeClient(["x", "If(x >= 0, x, -x)"]),
            task,
            mode="feedback",
            max_rounds=3,
            project_dir=PROJECT_DIR,
        )
        self.assertTrue(repaired["success"])
        self.assertEqual(repaired["rounds_used"], 2)

    def test_feedback_retries_timeout_and_unknown(self):
        task = {
            "id": "test_abs",
            "name": "test abs",
            "verifier": "z3",
            "spec": "abs",
            "output_format": "z3_expression",
            "prompt": "return abs",
        }
        with patch(
            "runner.verify_candidate",
            side_effect=[
                VerificationResult(TIMEOUT, False, "temporary timeout"),
                VerificationResult(VERIFIED, True, "ok"),
            ],
        ):
            timeout_then_verified = run_task(
                FakeClient(["candidate-1", "candidate-2"]), task,
                mode="feedback", max_rounds=3, project_dir=PROJECT_DIR,
            )
        with patch(
            "runner.verify_candidate",
            side_effect=[
                VerificationResult(UNKNOWN, False, "solver unknown"),
                VerificationResult(VERIFIED, True, "ok"),
            ],
        ):
            unknown_then_verified = run_task(
                FakeClient(["candidate-1", "candidate-2"]), task,
                mode="feedback", max_rounds=3, project_dir=PROJECT_DIR,
            )
        self.assertTrue(timeout_then_verified["success"])
        self.assertTrue(unknown_then_verified["success"])

    def test_api_error_stops(self):
        task = {
            "id": "test_abs",
            "name": "test abs",
            "verifier": "z3",
            "spec": "abs",
            "output_format": "z3_expression",
            "prompt": "return abs",
        }
        result = run_task(
            FakeClient([GLMClientError("safe failure")]),
            task,
            mode="feedback",
            max_rounds=3,
            project_dir=PROJECT_DIR,
        )
        self.assertFalse(result["success"])
        self.assertEqual(result["final_status"], "API_ERROR")

    def test_api_retries_transient_failure_then_succeeds(self):
        session = FakeSession(
            [
                requests.Timeout("first timeout"),
                FakeResponse(503, payload={"error": {"message": "busy"}}),
                FakeResponse(
                    200,
                    payload={"content": [{"type": "text", "text": "ok"}]},
                ),
            ]
        )
        client = GLMClient(
            GLMConfig(
                api_key="test-key",
                max_retries=3,
                retry_delay_seconds=0,
            )
        )
        client._session = session
        with patch("glm_client.time.sleep") as sleep:
            self.assertEqual(client.generate("hello"), "ok")
        self.assertEqual(session.calls, 3)
        self.assertEqual(sleep.call_count, 2)

    def test_api_retries_until_limit_then_raises(self):
        session = FakeSession(
            [
                FakeResponse(429, payload={"error": {"message": "rate limited"}}),
                FakeResponse(500, payload={"error": {"message": "down"}}),
                FakeResponse(503, payload={"error": {"message": "still down"}}),
            ]
        )
        client = GLMClient(
            GLMConfig(
                api_key="test-key",
                max_retries=3,
                retry_delay_seconds=0,
            )
        )
        client._session = session
        with patch("glm_client.time.sleep"):
            with self.assertRaisesRegex(GLMClientError, "after 3 attempts"):
                client.generate("hello")
        self.assertEqual(session.calls, 3)

    def test_api_retries_invalid_json_shape(self):
        session = FakeSession(
            [
                FakeResponse(200, payload=[]),
                FakeResponse(
                    200,
                    payload={"content": [{"type": "text", "text": "ok"}]},
                ),
            ]
        )
        client = GLMClient(
            GLMConfig(
                api_key="test-key",
                max_retries=2,
                retry_delay_seconds=0,
            )
        )
        client._session = session
        with patch("glm_client.time.sleep"):
            self.assertEqual(client.generate("hello"), "ok")
        self.assertEqual(session.calls, 2)

    def test_api_error_with_non_object_json_is_safe(self):
        session = FakeSession([FakeResponse(400, payload=[])])
        client = GLMClient(
            GLMConfig(
                api_key="test-key",
                max_retries=3,
                retry_delay_seconds=0,
            )
        )
        client._session = session
        with self.assertRaisesRegex(GLMClientError, "HTTP 400"):
            client.generate("hello")
        self.assertEqual(session.calls, 1)

    def test_screen_rejects_empty_verifier_field(self):
        accepted, _ = classify({"verifier": "", "prompt": "natural language"})
        self.assertFalse(accepted)

        accepted, _ = classify({"specification": "Write clean, readable code"})
        self.assertFalse(accepted)

    def test_screen_accepts_code_and_structured_tests(self):
        accepted, _ = classify(
            {"code": "def add(x): return x + 1", "tests": [{"input": 1, "output": 2}]}
        )
        self.assertTrue(accepted)

    def test_screen_samples_beyond_first_record(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "mixed.jsonl"
            path.write_text(
                '{"question": "natural-language question"}\n'
                '{"formal_spec": "Dafny method M() ensures true"}\n',
                encoding="utf-8",
            )
            report = screen(Path(directory))
        self.assertEqual(report["accepted"], 1)
        self.assertEqual(report["files"][0]["sampled_records"], 2)
        self.assertEqual(report["files"][0]["accepted_records"], 1)

    @unittest.skipUnless(importlib.util.find_spec("z3"), "z3-solver is not installed")
    def test_z3_task_timeout_configuration(self):
        task = {
            "verifier": "z3",
            "spec": "abs",
            "timeout_seconds": 1,
        }
        self.assertEqual(
            verify_candidate(task, "If(x >= 0, x, -x)", PROJECT_DIR).status,
            VERIFIED,
        )

    @unittest.skipUnless(importlib.util.find_spec("z3"), "z3-solver is not installed")
    def test_z3_rejects_non_positive_timeout(self):
        self.assertEqual(
            verify_z3_expression("abs", "x", timeout_seconds=0).status,
            VERIFIER_ERROR,
        )

    def test_verifier_registry_dispatches_to_a_new_backend(self):
        seen = []

        def adapter(task, candidate, project_dir):
            seen.append(candidate)
            return VerificationResult(VERIFIED, True, "stub verifier")

        verifiers.register_verifier("stub", adapter)
        self.addCleanup(verifiers._VERIFIERS.pop, "stub", None)
        self.assertIn("stub", verifiers.registered_verifiers())
        result = verify_candidate({"verifier": "stub"}, "candidate", PROJECT_DIR)
        self.assertEqual(result.status, VERIFIED)
        self.assertEqual(seen, ["candidate"])
        with self.assertRaises(ValueError):#重复注册会静默顶掉旧后端，必须报错
            verifiers.register_verifier("stub", adapter)

    def test_unknown_verifier_is_reported(self):
        result = verify_candidate({"verifier": "nope"}, "x", PROJECT_DIR)
        self.assertEqual(result.status, VERIFIER_ERROR)
        self.assertIn("nope", result.feedback)

    def test_non_string_verifier_does_not_crash_the_lookup(self):
        """A malformed task file must yield a status, not an unhashable-key crash."""
        for verifier in ([], {}, None, 3):
            with self.subTest(verifier=verifier):
                result = verify_candidate({"verifier": verifier}, "x", PROJECT_DIR)
                self.assertEqual(result.status, VERIFIER_ERROR)

    def test_builtin_registrations_are_present(self):
        self.assertEqual(verifiers.registered_verifiers(), ["dafny", "z3"])
        specs = set(verifiers.registered_z3_specs())
        self.assertTrue({"abs", "relu", "double", "max3"} <= specs)#原有四条
        self.assertTrue({"sign", "clamp_0_10", "square", "min_zero"} <= specs)#新增函数规格
        self.assertTrue({"nonneg", "even", "ge_x", "magnitude_x"} <= specs)#新增性质规格

    @unittest.skipUnless(importlib.util.find_spec("z3"), "z3-solver is not installed")
    def test_registered_z3_spec_is_used_for_verdict_and_witness(self):
        verifiers.register_z3_spec("triple", lambda z3, x, y: y == 3 * x)
        self.addCleanup(verifiers._Z3_SPECS.pop, "triple", None)
        self.assertEqual(verify_z3_expression("triple", "x + x + x").status, VERIFIED)
        rejected = verify_z3_expression("triple", "x + x")
        self.assertEqual(rejected.status, REJECTED)
        self.assertEqual(
            rejected.counterexample["expected_output"],
            3 * rejected.counterexample["x"],
        )

    def test_audit_only_runs_one_dafny_subcommand(self):
        """audit_dafny_source 不重跑 verify，最终阶段因此只付一次验证成本。"""
        seen = []

        def fake_run(dafny, subcommand, path, timeout_seconds):
            seen.append((subcommand, timeout_seconds))
            return verifiers._DafnyRun(False, 0, "auditor completed with 0 findings")

        with patch.object(verifiers, "_run_dafny", side_effect=fake_run):
            result = audit_dafny_source("lemma L() {}", timeout_seconds=30)
        self.assertEqual(result.status, VERIFIED)
        self.assertEqual(seen, [("audit", 30)])

    def test_audit_phase_shares_the_verify_timeout(self):
        """audit=True 时两个子进程共用一份 timeout_seconds，不能各用满一份。"""
        seen = []

        def fake_run(dafny, subcommand, path, timeout_seconds):
            seen.append((subcommand, timeout_seconds))
            if subcommand == "verify":
                time.sleep(1.2)
                return verifiers._DafnyRun(False, 0, "1 verified, 0 errors")
            return verifiers._DafnyRun(False, 0, "auditor completed with 0 findings")

        with patch.object(verifiers, "_run_dafny", side_effect=fake_run):
            result = verifiers.verify_dafny_source(
                "lemma L() {}", timeout_seconds=3, audit=True
            )
        self.assertEqual(result.status, VERIFIED)
        self.assertEqual([call[0] for call in seen], ["verify", "audit"])
        self.assertEqual(seen[0][1], 3)
        self.assertLess(seen[1][1], 3)  # audit 只拿到 verify 之后剩下的时间

    def test_audit_with_no_time_left_is_a_timeout(self):
        def fake_run(dafny, subcommand, path, timeout_seconds):
            time.sleep(1.1)
            return verifiers._DafnyRun(False, 0, "1 verified, 0 errors")

        with patch.object(verifiers, "_run_dafny", side_effect=fake_run):
            result = verifiers.verify_dafny_source(
                "lemma L() {}", timeout_seconds=1, audit=True
            )
        self.assertEqual(result.status, TIMEOUT)

    def test_audit_reports_a_trust_dependency(self):
        """真实 Dafny：带 assume {:axiom} 的程序能验证通过，但审计必须拒绝。"""
        clean = "lemma L(n: nat) ensures n >= 0 { }"
        cheating = "lemma L(n: nat) ensures 1 == 2 { assume {:axiom} false; }"
        self.assertEqual(audit_dafny_source(clean, timeout_seconds=120).status, VERIFIED)
        rejected = audit_dafny_source(cheating, timeout_seconds=120)
        self.assertEqual(rejected.status, REJECTED)
        self.assertIn("audit is not clean", rejected.feedback)


@unittest.skipUnless(importlib.util.find_spec("z3"), "z3-solver is not installed")
class Z3SpecGraphTests(unittest.TestCase):
    """规格注册表的自检，以及多规格任务的逐条判定。"""

    def _temp_spec(self, name, spec):
        verifiers.register_z3_spec(name, spec)
        self.addCleanup(verifiers._Z3_SPECS.pop, name, None)

    def test_every_builtin_spec_admits_an_output(self):
        self.assertEqual(verifiers.check_z3_specs(), [])

    def test_unsatisfiable_spec_is_caught_by_the_self_check(self):
        self._temp_spec("test_impossible", lambda z3, x, y: z3.And(y > x, y < x))
        failures = verifiers.check_z3_specs()
        self.assertTrue(any("test_impossible" in line for line in failures))

    def test_all_specs_must_hold_for_the_task_to_pass(self):
        result = verifiers.verify_z3_specs(
            ["abs", "nonneg", "ge_x", "magnitude_x"], "If(x >= 0, x, -x)"
        )
        self.assertEqual(result.status, VERIFIED)
        self.assertTrue(result.ok)
        self.assertEqual(
            {name: d["status"] for name, d in result.details["specs"].items()},
            {"abs": VERIFIED, "nonneg": VERIFIED, "ge_x": VERIFIED, "magnitude_x": VERIFIED},
        )

    def test_each_spec_is_reported_separately(self):
        """逐条报告：模型能看出坏在哪条性质上，而不是只知道整体失败。"""
        result = verifiers.verify_z3_specs(
            ["abs", "nonneg", "ge_x", "magnitude_x"], "x"
        )
        self.assertEqual(result.status, REJECTED)
        statuses = {
            name: detail["status"] for name, detail in result.details["specs"].items()
        }
        self.assertEqual(statuses["abs"], REJECTED)
        self.assertEqual(statuses["nonneg"], REJECTED)
        self.assertEqual(statuses["ge_x"], VERIFIED)#y == x 确实满足 y >= x
        self.assertEqual(statuses["magnitude_x"], VERIFIED)
        self.assertLess(result.counterexample["x"], 0)
        self.assertIn("abs: REJECTED", result.feedback)
        self.assertIn("ge_x: VERIFIED", result.feedback)

    def test_verifier_error_outranks_a_refutation(self):
        """注册表坏了要先报出来，不能被"模型答错"盖过去。"""
        self._temp_spec("test_impossible", lambda z3, x, y: z3.And(y > x, y < x))
        result = verifiers.verify_z3_specs(["nonneg", "test_impossible"], "x")
        self.assertEqual(result.status, VERIFIER_ERROR)

    def test_multi_spec_task_routes_through_the_adapter(self):
        task = {
            "verifier": "z3",
            "specs": ["relu", "nonneg", "ge_x"],
            "timeout_seconds": 30,
        }
        result = verify_candidate(task, "If(x >= 0, x, 0)", PROJECT_DIR)
        self.assertEqual(result.status, VERIFIED)
        self.assertEqual(len(result.details["specs"]), 3)

    def test_multi_spec_task_rejects_a_malformed_specs_field(self):
        task = {"verifier": "z3", "specs": "relu"}
        self.assertEqual(
            verify_candidate(task, "x", PROJECT_DIR).status, VERIFIER_ERROR
        )

    def test_multi_spec_reports_unknown_names_and_bad_candidates(self):
        self.assertEqual(
            verifiers.verify_z3_specs(["abs", "nope"], "x").status, VERIFIER_ERROR
        )
        self.assertEqual(verifiers.verify_z3_specs([], "x").status, VERIFIER_ERROR)
        self.assertEqual(
            verifiers.verify_z3_specs(["abs"], "not an expression").status,
            "FORMAT_ERROR",
        )

    def test_new_specs_accept_and_reject_the_expected_candidates(self):
        cases = [
            ("sign", "If(x > 0, 1, If(x < 0, -1, 0))", "If(x > 0, 1, -1)"),
            ("clamp_0_10", "If(x < 0, 0, If(x > 10, 10, x))", "If(x < 0, 0, x)"),
            ("square", "x * x", "x + x"),
            ("min_zero", "If(x < 0, x, 0)", "x"),
            ("negate", "-x", "x"),
            ("successor", "x + 1", "x"),
            ("even", "x + x", "x + x + 1"),
            ("nonpos", "-(x * x)", "x"),
            ("le_x", "x - 1", "x + 1"),
            ("bounded_1", "If(x > 0, 1, 0)", "x"),
        ]
        for spec, good, bad in cases:
            with self.subTest(spec=spec):
                self.assertEqual(verify_z3_expression(spec, good).status, VERIFIED)
                self.assertEqual(verify_z3_expression(spec, bad).status, REJECTED)


if __name__ == "__main__":
    unittest.main()