"""Run one GLM candidate directly or repair it with verifier feedback."""
#总调度器

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Protocol

from glm_client import GLMClient, GLMClientError
from verifiers import (
    FORMAT_ERROR,
    TIMEOUT,
    UNKNOWN,
    VERIFIER_ERROR,
    VerificationResult,
    extract_candidate,
    verify_candidate,
)

PROJECT_DIR = Path(__file__).resolve().parent
DEFAULT_TASKS = PROJECT_DIR / "tasks" / "formal_tasks.json"


class Generator(Protocol):#Protocol(协议)：只要具备规定方法(此处为 generate)即可作为接口，无需继承父类
    def generate(self, prompt: str, *, max_tokens: int | None = None) -> str: ...


@dataclass
class RoundRecord:
    round: int
    candidate: str | None#模型输出的候选
    verification: dict[str, Any]#验证结果


def load_tasks(path: Path = DEFAULT_TASKS) -> list[dict[str, Any]]:#读取 JSON 任务文件，并做基础检查(检查通用字段存在&去重)，不深入字段内部具体内容
    tasks = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(tasks, list) or not tasks:
        raise ValueError("task file must contain a non-empty JSON array")
    seen: set[str] = set()
    for task in tasks:
        required = {"id", "name", "verifier", "output_format", "prompt"}
        missing = required - set(task)
        if missing:
            raise ValueError(f"task is missing fields {sorted(missing)}: {task}")
        if task["id"] in seen:
            raise ValueError(f"duplicate task id: {task['id']}")
        seen.add(task["id"])
    return tasks


def run_task(
    client: Generator,
    task: dict[str, Any],
    *,
    mode: str,
    max_rounds: int,
    project_dir: Path = PROJECT_DIR,
) -> dict[str, Any]:
    if mode not in {"direct", "feedback"}:
        raise ValueError("mode must be 'direct' or 'feedback'")
    if max_rounds <= 0:
        raise ValueError("max_rounds must be positive")

    allowed_rounds = 1 if mode == "direct" else max_rounds
    prompt = _initial_prompt(task)
    rounds: list[RoundRecord] = []
    stop_reason = "round_limit"

    for round_number in range(1, allowed_rounds + 1):
        try:
            raw_output = client.generate(prompt)#1.调用 GLM
        except GLMClientError as exc:
            verification = VerificationResult("API_ERROR", False, str(exc))
            rounds.append(RoundRecord(round_number, None, verification.to_dict()))
            stop_reason = "api_error"
            break

        candidate, extraction_error = extract_candidate(#2.提取候选
            raw_output, task["output_format"]
        )
        if extraction_error:
            verification = VerificationResult(
                FORMAT_ERROR, False, extraction_error
            )
        else:
            assert candidate is not None
            verification = verify_candidate(task, candidate, project_dir)#3.调用验证器

        rounds.append(
            RoundRecord(round_number, candidate, verification.to_dict())
        )
        if verification.ok:#4.整体(不是单轮)停机条件
            stop_reason = "verified"
            break
        if mode == "direct":
            stop_reason = "direct_result"
            break
        # A timeout or an unknown result can be transient; feedback mode
        # should spend the remaining round budget retrying those cases.
        if verification.status == VERIFIER_ERROR:
            stop_reason = verification.status.lower()
            break
        if round_number == allowed_rounds:
            stop_reason = "round_limit"
            break

        prompt = _feedback_prompt(task, candidate, verification, round_number)

    final = rounds[-1].verification
    return {
        "task_id": task["id"],
        "task_name": task["name"],
        "mode": mode,
        "success": bool(final["ok"]),
        "final_status": final["status"],
        "stop_reason": stop_reason,
        "rounds_used": len(rounds),
        "rounds": [asdict(item) for item in rounds],
    }


def _initial_prompt(task: dict[str, Any]) -> str:
    return (
        "You are producing a candidate for a deterministic formal verifier.\n"
        "Follow the output format exactly; the verifier, not you, decides success.\n\n"
        + task["prompt"]
    )


def _feedback_prompt(
    task: dict[str, Any],
    candidate: str | None,
    verification: VerificationResult,
    round_number: int,
) -> str:
    previous = candidate if candidate is not None else "<unparseable output>"
    counterexample = (
        "\nCounterexample: " + json.dumps(verification.counterexample)
        if verification.counterexample
        else ""
    )
    return f"""You are repairing a candidate rejected by a deterministic formal verifier.

Original task:
{task['prompt']}

Previous candidate from round {round_number}:
{previous}

Verifier status: {verification.status}
Verifier feedback: {verification.feedback}{counterexample}

Return a complete replacement candidate in exactly the original required format.
Do not include an explanation or discuss the verifier feedback.
"""


def _select_tasks(#选择任务并验证存在
    tasks: list[dict[str, Any]], ids: list[str], run_all: bool
) -> list[dict[str, Any]]:
    if run_all:
        return tasks
    if not ids:
        raise ValueError("provide --task-id or --all")
    by_id = {task["id"]: task for task in tasks}
    missing = [task_id for task_id in ids if task_id not in by_id]
    if missing:
        raise ValueError(f"unknown task ids: {', '.join(missing)}")
    return [by_id[task_id] for task_id in ids]


def main() -> int:#该文件只支持 direct/feedback，sketch 应使用 sketch_runner.py
    parser = argparse.ArgumentParser(
        description="Evaluate GLM output with a deterministic verifier"
    )
    parser.add_argument("--mode", choices=["direct", "feedback"], default="direct")
    parser.add_argument("--task-id", action="append", default=[])
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--max-rounds", type=int, default=3)
    parser.add_argument("--tasks", type=Path, default=DEFAULT_TASKS)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()

    try:#0：全部成功；1：至少一个失败；2：配置/输入错误
        tasks = load_tasks(args.tasks)
        if args.list:
            for task in tasks:
                print(f"{task['id']}\t{task['verifier']}\t{task['name']}")
            return 0
        selected = _select_tasks(tasks, args.task_id, args.all)
        client = GLMClient()
        results = [
            run_task(
                client,
                task,
                mode=args.mode,
                max_rounds=args.max_rounds,
            )
            for task in selected
        ]
    except (ValueError, GLMClientError, OSError) as exc:
        print(json.dumps({"status": "CONFIG_ERROR", "error": str(exc)}))
        return 2

    rendered = json.dumps(results, indent=2, ensure_ascii=False)
    print(rendered)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n", encoding="utf-8")
    return 0 if all(result["success"] for result in results) else 1


if __name__ == "__main__":
    sys.exit(main())

#finish review：2026.9.14