"""Screen downloaded datasets for deterministic formal/code-verifier inputs."""
#非核心，暂时略过 review

from __future__ import annotations

import argparse
import csv
import gzip
import itertools
import json
import re
from collections.abc import Iterable, Mapping
from pathlib import Path
from typing import Any

PROJECT_DIR = Path(__file__).resolve().parent


def _default_data_root() -> Path:
    candidates = [
        PROJECT_DIR.parent / "glm-simple-evals-main" / "data",
        PROJECT_DIR.parent.parent / "glm-simple-evals-main" / "data",
    ]
    return next((path for path in candidates if path.is_dir()), candidates[0])


DEFAULT_DATA = _default_data_root()
DEFAULT_REPORT = PROJECT_DIR / "screening_report.json"

FORMAL_KEYS = {
    "formal_statement",
    "formal_spec",
    "specification",
    "verifier",
    "harness",
    "dafny",
    "lean",
    "z3",
}
CODE_KEYS = {"starter_code", "code", "function_signature"}
TEST_KEYS = {"test_cases", "private_test_cases", "input_output", "tests"}
FORMAL_MARKER_RE = re.compile(
    r"\b(?:dafny|lean4?|z3(?:py)?|smt(?:-lib)?|coq|isabelle|ensures|requires|"
    r"lemma|theorem|assert|invariant|precondition|postcondition)\b",
    flags=re.I,
)
SAMPLE_LIMIT = 25


def _read_records(path: Path, limit: int = SAMPLE_LIMIT) -> list[dict[str, Any]]:
    """Read at most ``limit`` object records from a supported data file."""

    if limit <= 0:
        return []

    name = path.name.lower()
    if name.endswith(".csv") or name.endswith(".tsv"):
        delimiter = "\t" if name.endswith(".tsv") else ","
        with path.open("r", encoding="utf-8-sig", newline="") as stream:
            return [
                dict(record)
                for record in itertools.islice(
                    csv.DictReader(stream, delimiter=delimiter), limit
                )
            ]

    if name.endswith(".jsonl") or name.endswith(".jsonl.gz"):
        opener = gzip.open if name.endswith(".jsonl.gz") else open
        with opener(path, "rt", encoding="utf-8") as stream:
            records: list[dict[str, Any]] = []
            for line in stream:
                if not line.strip():
                    continue
                value = json.loads(line)
                if isinstance(value, dict):
                    records.append(value)
                if len(records) >= limit:
                    break
            return records

    if name.endswith(".json"):
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, list):
            return [record for record in data[:limit] if isinstance(record, dict)]
        return [data] if isinstance(data, dict) else []

    return []


def first_record(path: Path) -> dict[str, Any]:
    """Backward-compatible helper returning the first object record."""

    records = _read_records(path, limit=1)
    return records[0] if records else {}


def _value_text(value: Any) -> str:
    if isinstance(value, str):
        return value.strip()
    if value is None or value is False:
        return ""
    if isinstance(value, (list, tuple, dict)):
        try:
            return json.dumps(value, ensure_ascii=False)
        except (TypeError, ValueError):
            return str(value)
    return str(value).strip()


def _non_empty(value: Any) -> bool:
    if isinstance(value, (list, tuple, dict)):
        return bool(value)
    return bool(_value_text(value))


def _contains_formal_marker(value: Any) -> bool:
    text = _value_text(value)
    if not text:
        return False
    return FORMAL_MARKER_RE.search(text) is not None


def _has_structured_tests(value: Any) -> bool:
    """Accept structured test data, but not a prose test description."""

    if isinstance(value, (list, tuple, dict)):
        return bool(value)
    if not isinstance(value, str) or not value.strip():
        return False
    try:
        decoded = json.loads(value)
    except (TypeError, ValueError):
        return False
    return isinstance(decoded, (list, dict)) and bool(decoded)


def classify(record: Mapping[str, Any] | Iterable[str]) -> tuple[bool, str]:
    """Classify one record using field values, not names alone.

    The iterable form is retained for callers of the old helper. Since it
    contains no values, it cannot prove that a field has usable evidence and
    is consequently rejected.
    """

    if isinstance(record, Mapping):
        values = {
            str(key).lower().strip(): value for key, value in record.items() if key
        }
    else:
        values = {str(key).lower().strip(): None for key in record if key}

    formal_fields = [
        key
        for key in FORMAL_KEYS
        if key in values
        and _non_empty(values[key])
        and _contains_formal_marker(values[key])
    ]
    if formal_fields:
        return (
            True,
            "contains non-empty formal evidence in: "
            + ", ".join(sorted(formal_fields)),
        )

    code_fields = [
        key for key in CODE_KEYS if key in values and _non_empty(values[key])
    ]
    test_fields = [
        key
        for key in TEST_KEYS
        if key in values and _has_structured_tests(values[key])
    ]
    if code_fields and test_fields:
        return (
            True,
            "contains non-empty code and structured tests in: "
            + ", ".join(sorted(code_fields))
            + " + "
            + ", ".join(sorted(test_fields)),
        )
    return (
        False,
        "no non-empty formal evidence or structured code-and-tests fields",
    )


def screen(root: Path) -> dict[str, Any]:
    supported = {".csv", ".tsv", ".json", ".jsonl", ".gz"}
    records: list[dict[str, Any]] = []
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        if path.suffix.lower() not in supported:
            continue
        try:
            samples = _read_records(path)
            decisions = [classify(sample) for sample in samples]
            accepted_records = sum(1 for accepted, _ in decisions if accepted)
            accepted = accepted_records > 0
            if accepted:
                reason = "; ".join(
                    sorted({reason for decision, reason in decisions if decision})
                )
            elif not samples:
                reason = "no object records found in the sample"
            else:
                reason = decisions[0][1]
            fields = sorted(
                {
                    str(key)
                    for sample in samples
                    for key in sample.keys()
                }
            )
            records.append(
                {
                    "path": str(path.relative_to(root)),
                    "accepted": accepted,
                    "reason": reason,
                    "fields": fields,
                    "sampled_records": len(samples),
                    "accepted_records": accepted_records,
                }
            )
        except Exception as exc:
            records.append(
                {
                    "path": str(path.relative_to(root)),
                    "accepted": False,
                    "reason": f"could not inspect: {type(exc).__name__}: {exc}",
                    "fields": [],
                    "sampled_records": 0,
                    "accepted_records": 0,
                }
            )
    accepted_count = sum(1 for item in records if item["accepted"])
    return {
        "data_root": str(root.resolve()),
        "files_inspected": len(records),
        "accepted": accepted_count,
        "rejected": len(records) - accepted_count,
        "policy": (
            "Accept only records with non-empty formal evidence or structured "
            "code plus deterministic tests; reject natural-language datasets."
        ),
        "files": records,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("data_root", nargs="?", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--output", type=Path, default=DEFAULT_REPORT)
    args = parser.parse_args()
    if not args.data_root.is_dir():
        parser.error(f"data directory does not exist: {args.data_root}")
    report = screen(args.data_root)
    args.output.write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(
        f"inspected={report['files_inspected']} accepted={report['accepted']} "
        f"rejected={report['rejected']} report={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
