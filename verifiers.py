"""Deterministic verifier adapters used by the two evaluation modes."""
#判定模型生成的候选内容是否满足固定的数学或程序规格

from __future__ import annotations

import ast
import operator
import os
import re
import shutil
import subprocess
import tempfile
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable


VERIFIED = "VERIFIED"
REJECTED = "REJECTED"
FORMAT_ERROR = "FORMAT_ERROR"
TIMEOUT = "TIMEOUT"
UNKNOWN = "UNKNOWN"
VERIFIER_ERROR = "VERIFIER_ERROR"


@dataclass
class VerificationResult:
    status: str
    ok: bool
    feedback: str
    counterexample: dict[str, int] | None = None
    elapsed_ms: int = 0#耗时
    details: dict[str, Any] | None = None#多规格验证的逐条结果、求解器调用次数等

    def to_dict(self) -> dict[str, Any]:#转为 JSON，方便输出
        return asdict(self)


#验证器注册表：新增验证器或 Z3 规格不必再修改 verify_candidate 的分支
VerifierAdapter = Callable[[dict[str, Any], str, Path], VerificationResult]#验证器注册表
Z3Spec = Callable[[Any, Any, Any], Any]#(z3 模块, 输入 x, 输出 y) -> 约束 #题目注册表

_VERIFIERS: dict[str, VerifierAdapter] = {}
_Z3_SPECS: dict[str, Z3Spec] = {}#规格名 -> 具体规格


def register_verifier(name: str, adapter: VerifierAdapter) -> None:#注册验证器，若重复则报错
    """Register one verifier backend under a task's ``verifier`` value."""
    if name in _VERIFIERS:
        raise ValueError(f"verifier already registered: {name}")
    _VERIFIERS[name] = adapter


def register_z3_spec(name: str, spec: Z3Spec) -> None:#注册题目，若重复则报错
    """Register one fixed Z3 specification constraining output y from input x."""
    if name in _Z3_SPECS:
        raise ValueError(f"Z3 specification already registered: {name}")
    _Z3_SPECS[name] = spec


def registered_verifiers() -> list[str]:
    return sorted(_VERIFIERS)


def registered_z3_specs() -> list[str]:
    return sorted(_Z3_SPECS)


def check_z3_specs(
    samples: tuple[int, ...] = (-101, -7, -1, 0, 1, 7, 101),
) -> list[str]:#抽样自检：每条规格在这些输入上都要有合法输出
    """Sample-check that every registered spec still admits an output for each x.

    A spec with no witness can never be satisfied, so such a task would report
    ``REJECTED`` no matter what the model answers.
    """
    try:
        import z3
    except ImportError:
        return ["z3-solver is not installed; run: pip install -r requirements.txt"]
    failures: list[str] = []
    for name, spec in sorted(_Z3_SPECS.items()):
        for x0 in samples:
            try:
                _z3_witness(spec, x0, z3)
            except RuntimeError as exc:
                failures.append(f"{name} at x={x0}: {exc}")
                break
    return failures


def extract_candidate(text: str, output_format: str) -> tuple[str | None, str | None]:#从模型原始回复中提取候选内容(初步格式提取)
    if not text or not text.strip():
        return None, "model returned empty output"

    cleaned = re.sub(r"<think>.*?</think>", "", text, flags=re.S | re.I).strip()#去除思考区块
    blocks = re.findall(r"```(?:[A-Za-z0-9_+.-]+)?\s*\n(.*?)```", cleaned, re.S)#识别 md 代码块，只取最后一个
    if blocks:
        cleaned = blocks[-1].strip()

    if output_format == "z3_expression":#z3：验证模型生成的数学表达式；必须只有一行，(此处未验证)不可为自然语言
        lines = [line.strip() for line in cleaned.splitlines() if line.strip()]
        if len(lines) != 1:
            return None, "expected exactly one expression line"
        expression = lines[0].rstrip(";")
        if expression.startswith("lambda ") and ":" in expression:
            expression = expression.split(":", 1)[1].strip()
        return expression, None

    if output_format == "dafny_body":
        if not cleaned:
            return None, "expected Dafny statements"
        return cleaned, None

    return None, f"unknown output format: {output_format}"


def verify_candidate(task: dict[str, Any], candidate: str, project_dir: Path) -> VerificationResult:#查注册表后传给对应验证器接口
    verifier = task.get("verifier")
    #任务文件里的 verifier 可能不是字符串；dict.get 遇到不可哈希的值会抛 TypeError
    adapter = _VERIFIERS.get(verifier) if isinstance(verifier, str) else None
    if adapter is None:
        return VerificationResult(
            VERIFIER_ERROR, False, f"unsupported verifier: {verifier!r}"
        )
    return adapter(task, candidate, project_dir)


def _z3_adapter(#z3 验证器接口
    task: dict[str, Any], candidate: str, project_dir: Path
) -> VerificationResult:
    timeout_seconds = float(task.get("timeout_seconds", 30))
    specs = task.get("specs")#多规格任务：每条单独判定，全部成立才算通过
    if specs is not None:
        if not isinstance(specs, list) or not all(isinstance(n, str) for n in specs):
            return VerificationResult(
                VERIFIER_ERROR, False, "task field 'specs' must be a list of names"
            )
        return verify_z3_specs(specs, candidate, timeout_seconds=timeout_seconds)
    return verify_z3_expression(
        task["spec"],
        candidate,
        timeout_seconds=timeout_seconds,
    )


def _dafny_adapter(#dafny 验证器接口
    task: dict[str, Any], candidate: str, project_dir: Path
) -> VerificationResult:
    return verify_dafny(
        project_dir / task["template_path"],
        candidate,
        timeout_seconds=int(task.get("timeout_seconds", 120)),
        audit=bool(task.get("audit", True)),
    )


@dataclass
class _Z3Session:#一次验证里共用的 z3 环境和已解析好的候选表达式
    z3: Any
    x: Any
    term: Any


def _open_z3_session(
    expression: str, started: float
) -> tuple["_Z3Session | None", VerificationResult | None]:
    """Import z3 and parse the candidate once, so every spec reuses the same term."""
    try:
        import z3
    except ImportError:
        return None, VerificationResult(
            VERIFIER_ERROR,
            False,
            "z3-solver is not installed; run: pip install -r requirements.txt",
        )
    try:
        x = z3.Int("x")
        term = _build_z3_expression(expression, x, z3)#模型给出的字符串转换成 Z3 表达式，若为自然语言则报错
    except Exception as exc:
        return None, VerificationResult(
            FORMAT_ERROR,
            False,
            f"candidate is not a valid restricted expression: {exc}",
            elapsed_ms=_elapsed_ms(started),
        )
    return _Z3Session(z3, x, term), None


def _counterexample(
    session: _Z3Session, spec: Z3Spec, x0: int
) -> dict[str, int]:#给定反例输入，记录候选输出和该规格要求的正确输出
    z3 = session.z3
    wrong = z3.simplify(
        z3.substitute(session.term, (session.x, z3.IntVal(x0)))
    ).as_long()
    return {"x": x0, "candidate_output": wrong, "expected_output": _z3_witness(spec, x0, z3)}


def _prove_spec(
    session: _Z3Session, spec_name: str, spec: Z3Spec, *, timeout_seconds: float
) -> tuple[str, str, dict[str, int] | None]:
    """Run one solver query: does the candidate satisfy this spec for every x?"""
    z3 = session.z3
    solver = z3.Solver()
    # Z3's default is to wait indefinitely.  A model-supplied nonlinear expression must not be able to hang a benchmark run, so enforce the task-level deadline in milliseconds (Z3 reports an expired deadline as ``unknown``).
    solver.set(timeout=max(1, round(timeout_seconds * 1000)))
    solver.add(z3.Not(spec(z3, session.x, session.term)))#反证法：让 z3 试找出使候选表达式不满足规格(任务要求)的 x；规格(题目)来自注册表，较复杂的任务适合用 Dafny 或新的验证器
    result = solver.check()
    if result == z3.unsat:#找不到：通过
        return (
            VERIFIED,
            f"Z3 proved the expression satisfies '{spec_name}' for every integer x",
            None,
        )
    if result == z3.unknown:#无法判断
        return UNKNOWN, f"Z3 returned unknown: {solver.reason_unknown()}", None

    model = solver.model()
    x0 = model.eval(session.x, model_completion=True).as_long()
    found = _counterexample(session, spec, x0)
    #找到，记录具体 x，候选结果(实际输出)，期望结果(目标输出)
    return (
        REJECTED,
        f"counterexample: x={x0}, candidate={found['candidate_output']},"
        f" expected={found['expected_output']}",
        found,
    )


def verify_z3_expression(
    spec_name: str,
    expression: str,
    *,
    timeout_seconds: float = 30.0,
) -> VerificationResult:
    started = time.perf_counter()
    session, failure = _open_z3_session(expression, started)
    if failure is not None:
        return failure
    assert session is not None

    spec = _Z3_SPECS.get(spec_name)#查看有没有对应题
    if spec is None:
        return VerificationResult(
            VERIFIER_ERROR,
            False,
            f"unknown Z3 specification: {spec_name}",
            elapsed_ms=_elapsed_ms(started),
        )

    if timeout_seconds <= 0:
        return VerificationResult(
            VERIFIER_ERROR,
            False,
            "Z3 timeout_seconds must be positive",
            elapsed_ms=_elapsed_ms(started),
        )

    status, feedback, counterexample = _prove_spec(
        session, spec_name, spec, timeout_seconds=timeout_seconds
    )
    return VerificationResult(
        status,
        status == VERIFIED,
        feedback,
        counterexample=counterexample,
        elapsed_ms=_elapsed_ms(started),
    )


def verify_z3_specs(
    spec_names: list[str],
    expression: str,
    *,
    timeout_seconds: float = 30.0,
) -> VerificationResult:
    """Check one candidate against several specs, reporting each separately.

    Every spec gets its own solver query and its own verdict, so a task can
    demand a conjunction of properties and still tell the model exactly which
    one broke.  The whole call passes only when every spec holds.
    """
    started = time.perf_counter()
    names = list(dict.fromkeys(spec_names))#去重保序
    if not names:
        return VerificationResult(
            VERIFIER_ERROR, False, "at least one Z3 specification is required"
        )
    missing = [name for name in names if name not in _Z3_SPECS]
    if missing:
        return VerificationResult(
            VERIFIER_ERROR,
            False,
            f"unknown Z3 specification: {', '.join(sorted(missing))}",
        )
    if timeout_seconds <= 0:
        return VerificationResult(
            VERIFIER_ERROR, False, "Z3 timeout_seconds must be positive"
        )

    session, failure = _open_z3_session(expression, started)
    if failure is not None:
        return failure
    assert session is not None

    outcomes: dict[str, dict[str, Any]] = {}
    for name in names:
        try:
            status, feedback, found = _prove_spec(
                session, name, _Z3_SPECS[name], timeout_seconds=timeout_seconds
            )
        except RuntimeError as exc:#规格本身无解，属于注册表配置错误
            outcomes[name] = {"status": VERIFIER_ERROR, "feedback": str(exc)}
            continue
        outcomes[name] = {"status": status, "feedback": feedback}
        if found is not None:
            outcomes[name]["counterexample"] = found

    statuses = {name: outcomes[name]["status"] for name in names}
    #VERIFIER_ERROR > REJECTED > UNKNOWN > VERIFIED：先报最该人工介入的问题
    for candidate_status in (VERIFIER_ERROR, REJECTED, UNKNOWN):
        if candidate_status in statuses.values():
            overall = candidate_status
            break
    else:
        overall = VERIFIED

    first_counterexample = next(
        (
            outcomes[name]["counterexample"]
            for name in names
            if outcomes[name].get("counterexample")
        ),
        None,
    )
    lines = [
        f"{name}: {outcomes[name]['status']}"
        + (
            " — " + outcomes[name]["feedback"]
            if outcomes[name]["status"] != VERIFIED
            else ""
        )
        for name in names
    ]
    return VerificationResult(
        overall,
        overall == VERIFIED,
        "\n".join(lines),
        counterexample=first_counterexample,
        elapsed_ms=_elapsed_ms(started),
        details={"specs": {name: outcomes[name] for name in names}},
    )


def _build_z3_expression(expression: str, x: Any, z3: Any) -> Any:#将字符串解析为 Z3 表达式
    binary = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul}
    comparisons = {
        ast.Eq: operator.eq,
        ast.NotEq: operator.ne,
        ast.Lt: operator.lt,
        ast.LtE: operator.le,
        ast.Gt: operator.gt,
        ast.GtE: operator.ge,
    }

    def visit(node: ast.AST) -> Any:#遍历，只允许白名单语法
        if isinstance(node, ast.Expression):
            return visit(node.body)
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return z3.IntVal(node.value)
        if isinstance(node, ast.Name) and node.id == "x":
            return x
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = visit(node.operand)
            return value if isinstance(node.op, ast.UAdd) else -value
        if isinstance(node, ast.BinOp) and type(node.op) in binary:
            return binary[type(node.op)](visit(node.left), visit(node.right))
        if isinstance(node, ast.Compare) and len(node.ops) == 1 and type(node.ops[0]) in comparisons:
            return comparisons[type(node.ops[0])](
                visit(node.left), visit(node.comparators[0])
            )
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "If"
            and len(node.args) == 3
            and not node.keywords
        ):
            return z3.If(*(visit(arg) for arg in node.args))
        raise ValueError(f"disallowed syntax: {ast.dump(node, include_attributes=False)}")

    term = visit(ast.parse(expression, mode="eval"))
    if not z3.is_int(term):
        raise ValueError("candidate must be integer-valued")
    return term


def _z3_witness(spec: Z3Spec, x0: int, z3: Any) -> int:#算期望结果(已经找到反例后)
    y = z3.Int("expected_y")
    solver = z3.Solver()
    solver.add(spec(z3, z3.IntVal(x0), y))
    if solver.check() != z3.sat:
        raise RuntimeError("the fixed specification has no output witness")
    return solver.model().eval(y, model_completion=True).as_long()


def verify_dafny(#接收模板和方法体(提取后的模型输出，替换{{CANDIDATE}})
    template_path: Path,
    candidate: str,
    *,
    timeout_seconds: int,
    audit: bool,
) -> VerificationResult:
    started = time.perf_counter()
    if not template_path.is_file():
        return VerificationResult(
            VERIFIER_ERROR, False, f"Dafny template not found: {template_path}"
        )

    forbidden = re.search(#防止模型修改验证环境或引入未经证明的假设，遇到直接REJECTED
        r"\b(?:assume|axiom|extern|include|module)\b|\{:\s*axiom\s*\}",
        candidate,
        flags=re.I,
    )
    if forbidden:
        return VerificationResult(
            REJECTED,
            False,
            f"candidate contains forbidden trust escape: {forbidden.group(0)}",
            elapsed_ms=_elapsed_ms(started),
        )

    template = template_path.read_text(encoding="utf-8")
    if "{{CANDIDATE}}" not in template:
        return VerificationResult(
            VERIFIER_ERROR,
            False,
            "Dafny template has no {{CANDIDATE}} placeholder",
            elapsed_ms=_elapsed_ms(started),
        )
    program = template.replace("{{CANDIDATE}}", candidate)

    dafny = _dafny_executable()
    if dafny is None:
        return VerificationResult(
            VERIFIER_ERROR,
            False,
            "dafny is not installed or configured; set DAFNY_BIN or install it on PATH",
            elapsed_ms=_elapsed_ms(started),
        )

    return verify_dafny_source(
        program,
        timeout_seconds=timeout_seconds,
        audit=audit,
    )


@dataclass
class _DafnyRun:#一次 Dafny 子命令调用的原始结果
    timed_out: bool
    returncode: int
    output: str


def _run_dafny(dafny: str, subcommand: str, path: Path, timeout_seconds: int) -> _DafnyRun:
    """Run one Dafny subcommand against an already written source file."""
    try:
        process = subprocess.run(
            [dafny, subcommand, str(path)],
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        return _DafnyRun(True, -1, "")
    return _DafnyRun(False, process.returncode, (process.stdout + process.stderr).strip())


def _audit_verdict(run: _DafnyRun, timeout_seconds: int, started: float) -> VerificationResult:
    """Turn one ``dafny audit`` run into a verdict;审计不干净一律不算成功。"""
    if run.timed_out:
        return VerificationResult(
            TIMEOUT,
            False,
            f"Dafny audit exceeded {timeout_seconds} seconds",
            elapsed_ms=_elapsed_ms(started),
        )
    findings = re.search(r"completed with (\d+) finding", run.output)
    if run.returncode != 0 or not findings or findings.group(1) != "0":
        return VerificationResult(
            REJECTED,
            False,
            "Dafny audit is not clean: " + run.output,
            elapsed_ms=_elapsed_ms(started),
        )
    return VerificationResult(
        VERIFIED,
        True,
        run.output or "Dafny audit found no trust dependency",
        elapsed_ms=_elapsed_ms(started),
    )


def verify_dafny_source(#适配 sketch，接收一整段 Dafny 源码(方法体&辅助引理&变量及类型声明&前后置条件约束&函数/方法/引理定义)
    program: str,
    *,
    timeout_seconds: int,
    audit: bool,
) -> VerificationResult:
    """Verify a complete Dafny source string.

    This is used by Sketch's internal stages after assembling a fixed harness.
    Callers must perform candidate safety checks before passing source here.
    ``timeout_seconds`` bounds the whole call: with ``audit=True`` the audit
    phase only gets whatever the verification phase left over.
    """
    #不会检查源码中是否包含 assume、axiom 或extern，要求调用者先完成安全检查
    started = time.perf_counter()
    dafny = _dafny_executable()
    if dafny is None:
        return _missing_dafny(started)

    with tempfile.TemporaryDirectory(prefix="glm_verify_") as temp_dir:
        path = Path(temp_dir) / "candidate.dfy"
        path.write_text(program, encoding="utf-8")#写入临时 .dfy 文件
        run = _run_dafny(dafny, "verify", path, timeout_seconds)
        if run.timed_out:
            return VerificationResult(
                TIMEOUT,
                False,
                f"Dafny verification exceeded {timeout_seconds} seconds",
                elapsed_ms=_elapsed_ms(started),
            )
        if run.returncode != 0:
            return VerificationResult(
                REJECTED,
                False,
                run.output or "Dafny rejected the candidate",
                elapsed_ms=_elapsed_ms(started),
            )

        if audit:#Dafny 自带 audit；两个子进程共用同一份 timeout_seconds 预算
            left = timeout_seconds - (time.perf_counter() - started)
            if left < 1.0:
                return VerificationResult(
                    TIMEOUT,
                    False,
                    f"Dafny audit had no time left within {timeout_seconds} seconds",
                    elapsed_ms=_elapsed_ms(started),
                )
            audited = _audit_verdict(
                _run_dafny(dafny, "audit", path, max(1, int(left))),
                timeout_seconds,
                started,
            )
            if not audited.ok:
                return audited

        return VerificationResult(
            VERIFIED,
            True,
            run.output or "Dafny verified and audited the candidate",
            elapsed_ms=_elapsed_ms(started),
        )


def audit_dafny_source(program: str, *, timeout_seconds: int) -> VerificationResult:
    """Run only ``dafny audit`` on a program that已经单独验证过。

    Sketch's final stage verifies and audits as two separate steps so each one
    keeps its own status and its own slice of the time budget; re-running
    ``dafny verify`` inside the audit call would just pay for it twice.
    """
    started = time.perf_counter()
    dafny = _dafny_executable()
    if dafny is None:
        return _missing_dafny(started)

    with tempfile.TemporaryDirectory(prefix="glm_audit_") as temp_dir:
        path = Path(temp_dir) / "candidate.dfy"
        path.write_text(program, encoding="utf-8")
        return _audit_verdict(
            _run_dafny(dafny, "audit", path, timeout_seconds), timeout_seconds, started
        )


def _missing_dafny(started: float) -> VerificationResult:
    return VerificationResult(
        VERIFIER_ERROR,
        False,
        "dafny is not installed or configured; set DAFNY_BIN or install it on PATH",
        elapsed_ms=_elapsed_ms(started),
    )


def _dafny_executable() -> str | None:#查找 Dafny：DAFNY_BIN 环境变量 -> PATH 中的 dafny -> tools/dafny-4.11.0/dafny/Dafny.exe
    configured = os.environ.get("DAFNY_BIN", "").strip()
    if configured:
        return configured if Path(configured).is_file() else None
    on_path = shutil.which("dafny")
    if on_path:
        return on_path
    bundled = Path(__file__).resolve().parent / "tools" / "dafny-4.11.0" / "dafny" / "Dafny.exe"
    return str(bundled) if bundled.is_file() else None


def _elapsed_ms(started: float) -> int:
    return round((time.perf_counter() - started) * 1000)


#内置默认注册项，外部模块可以再调用 register_verifier / register_z3_spec 扩展。
register_verifier("z3", _z3_adapter)
register_verifier("dafny", _dafny_adapter)

#—— 完整函数规格：对每个 x 都唯一确定 y ——
register_z3_spec(
    "abs", lambda z3, x, y: z3.And(y >= x, y >= -x, z3.Or(y == x, y == -x))
)
register_z3_spec(
    "relu", lambda z3, x, y: z3.And(y >= 0, y >= x, z3.Or(y == 0, y == x))
)
register_z3_spec("double", lambda z3, x, y: y == x + x)
register_z3_spec(
    "max3",
    lambda z3, x, y: z3.And(
        y >= x,
        y >= 2 * x,
        y >= 6,
        z3.Or(y == x, y == 2 * x, y == 6),
    ),
)
register_z3_spec("negate", lambda z3, x, y: y + x == 0)
register_z3_spec("successor", lambda z3, x, y: y == x + 1)
register_z3_spec("square", lambda z3, x, y: y == x * x)
register_z3_spec(#min(x, 0)：用上下界加取值集合刻画，而不是直接写出答案
    "min_zero", lambda z3, x, y: z3.And(y <= 0, y <= x, z3.Or(y == 0, y == x))
)
register_z3_spec(
    "sign",
    lambda z3, x, y: z3.And(
        z3.Implies(x < 0, y == -1),
        z3.Implies(x == 0, y == 0),
        z3.Implies(x > 0, y == 1),
    ),
)
register_z3_spec(
    "clamp_0_10",
    lambda z3, x, y: z3.And(
        z3.Implies(x < 0, y == 0),
        z3.Implies(z3.And(x >= 0, x <= 10), y == x),
        z3.Implies(x > 10, y == 10),
    ),
)

#—— 单条性质规格：只约束一个方面，适合用 specs 组合出更严的要求 ——
register_z3_spec("nonneg", lambda z3, x, y: y >= 0)
register_z3_spec("nonpos", lambda z3, x, y: y <= 0)
register_z3_spec("even", lambda z3, x, y: y % 2 == 0)
register_z3_spec("ge_x", lambda z3, x, y: y >= x)
register_z3_spec("le_x", lambda z3, x, y: y <= x)
register_z3_spec("magnitude_x", lambda z3, x, y: z3.Or(y == x, y == -x))
register_z3_spec("bounded_1", lambda z3, x, y: z3.And(y >= -1, y <= 1))
register_z3_spec("bounded_10", lambda z3, x, y: z3.And(y >= -10, y <= 10))

#finish review：2026.9.14
#finish review version-"把验证器写成注册表" 2026.9.21