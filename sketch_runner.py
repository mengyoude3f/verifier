"""Three-stage Sketch runner for decomposed Dafny proofs.

The model supplies a proof sketch containing named ``HOLE_*`` markers.  Only
the runner may replace those markers with internal stubs; a final assembly is
always checked without stubs and then audited.
"""
#Sketch 特供 runner(附解析器(着重于分析结构而非计算))

from __future__ import annotations

import json
import re
import argparse
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Protocol

from glm_client import GLMClientError
from verifiers import (
    FORMAT_ERROR,
    REJECTED,
    TIMEOUT,
    UNKNOWN,
    VERIFIER_ERROR,
    VERIFIED,
    VerificationResult,
    audit_dafny_source,
    extract_candidate,
    verify_dafny_source,
)


SKETCH_FORMAT_ERROR = "SKETCH_FORMAT_ERROR"
HOLE_FAILED = "HOLE_FAILED"#某个 hole 在预算内始终失败
ASSEMBLY_ERROR = "ASSEMBLY_ERROR"#最终组装后的程序验证失败
AUDIT_REJECTED = "AUDIT_REJECTED"#普通验证通过，但 audit 不通过
API_ERROR = "API_ERROR"#GLM 调用失败
BUDGET_EXHAUSTED = "BUDGET_EXHAUSTED"#模型调用次数用尽(不是时间耗尽)
#底层原因优先于阶段标签：这些状态说明的是设施故障，不是模型没证出来
_INFRASTRUCTURE_STATUSES = frozenset({TIMEOUT, UNKNOWN, VERIFIER_ERROR})#验证器问题，而非回答模型问题
_FORBIDDEN = re.compile(
    r"\b(?:assume|axiom|extern|include|module|method|function)\b|"
    #会跳过或缩小验证范围的"开发期"属性：{:verify false} 让 Dafny 整条跳过，
    #assert {:only} 把同一成员里其余断言降级成假设，{:nowarn} 压掉相关告警；
    #{:timeLimit}/{:rlimit} 不影响可靠性，但让模型能自行放大验证开销、逼出超时
    r"\{:\s*(?:axiom|verify|only|nowarn|timeLimit|rlimit)\b",
    re.I,
)
_HOLE = re.compile(r"\bHOLE_([A-Za-z_][A-Za-z0-9_]*)\b")
_LEMMA_KEYWORD = "lemma"#标识引理的关键字，方便查找


class Generator(Protocol):
    def generate(self, prompt: str, *, max_tokens: int | None = None) -> str: ...


class _BudgetExhausted(RuntimeError):#模型调用次数用尽(不是时间耗尽)
    """A stage stopped because the total time or model-call budget ran out."""

    def __init__(self, message: str, status: str):
        super().__init__(message)
        self.status = status


@dataclass
class HoleRecord:
    name: str
    status: str#最终状态
    candidate: str | None#最后一个候选
    rounds: int
    verification: dict[str, Any] | None#最后一次候选结果
    attempts: list[dict[str, Any]] = field(default_factory=list)#每一轮的详细记录
    depth: int = 1#嵌套层级，根草图的洞算第 1 层
    parent: str | None = None#被哪个 hole 展开出来
    kind: str = "leaf"#leaf(直接写出证明体) 或 expanded(交回子草图)
    children: list[str] = field(default_factory=list)#展开出的子洞


def _task_int(task: dict[str, Any], name: str, default: int) -> int:
    value = int(task.get(name, default))
    if value <= 0:
        raise ValueError(f"{name} must be positive")
    return value


def _is_identifier_char(char: str) -> bool:#识别合法字符：1.是字符串；2.非空；3.是字母、数字或“_” 、“'”
    #Dafny 标识符允许撇号(如 x')，所以撇号不一定是字符字面量的开头
    return bool(char) and (char.isalnum() or char in "_'")


def _is_keyword_at(source: str, index: int, word: str) -> bool:#识别 source(源码) 中某 index(下标) 处是否为某 word(关键字)：1.找到关键字字段；2.前一个字符&后一个字符不是合法的(说明确实是独立的关键字而非某长字段的一部分)
    if not source.startswith(word, index):
        return False
    before = source[index - 1] if index else ""
    after = source[index + len(word)] if index + len(word) < len(source) else ""
    return not _is_identifier_char(before) and not _is_identifier_char(after)


def _skip_literal(source: str, index: int, *, verbatim: bool) -> int:#解析时跳过字符串/字符字面量(直接写死的值)，防止可能出现的“{”、关键字等导致的解析错误
    #index：字面量开始的位置；verbatim：是否为逐字字符串(1.格式为@""；2.\不表示转义；3.字符串内""表示")(与普通字符/字符串字面量的规定不同(\表示转义)，解析方式也不同)：
    """Return the index just past the string or char literal opening at ``index``."""
    quote = source[index]#取开头的引号
    index += 1
    while index < len(source):
        char = source[index]
        if verbatim:
            if char == quote:
                if source.startswith(quote * 2, index):#@"" 里用 "" 转义引号 #逐字字符串中""并非终止，而是字符串的一部分
                    index += 2
                    continue
                return index + 1#逐字字符串中不连续的"标志着终止，直接返回
        elif char == "\\":
            index += 2
            continue
        elif char == quote:#非逐字字符串的"标志着终止，直接返回
            return index + 1
        index += 1
    return -1


def _scan_declarations(#格式解析入口，返回当前深度下的 lemma(引理) 和 group(组，深度增加)
    source: str,
) -> tuple[list[int], list[tuple[int, int]], str | None]:
    """Locate top-level ``lemma`` keywords and top-level brace groups.

    Depth is tracked character by character so nested blocks stay inside one
    group, and literals are skipped so a brace in a string cannot shift it.
    """
    lemmas: list[int] = []
    groups: list[tuple[int, int]] = []
    depth = 0#当前深度
    start = 0#最后一个 group 的起始位置(即最后一个非字符串/字符字面量内的 '{')
    index = 0#实时解析到的位置
    while index < len(source):
        char = source[index]
        if char == "@" and source.startswith('@"', index):#跳过逐字字符串
            index = _skip_literal(source, index + 1, verbatim=True)
        elif char == '"':#跳过普通字符串字面量
            index = _skip_literal(source, index, verbatim=False)
        elif char == "'" and not _is_identifier_char(source[index - 1] if index else ""):
            index = _skip_literal(source, index, verbatim=False)#跳过字符字面量(n' 不算字符字面量，这种情况已排除)
        elif char == "{":#group 开始，depth++
            if depth == 0:
                start = index
            depth += 1
            index += 1
        elif char == "}":#group 结束，depth--
            depth -= 1
            if depth < 0:
                return [], [], "sketch has an unbalanced closing brace"
            if depth == 0:#只返回 depth == 0(表层) 的 group 位置
                groups.append((start, index + 1))
            index += 1
        elif depth == 0 and _is_keyword_at(source, index, _LEMMA_KEYWORD):#返回引理位置
            lemmas.append(index)
            index += len(_LEMMA_KEYWORD)
        else:
            index += 1
        if index < 0:
            return [], [], "sketch has an unterminated string or character literal"
    if depth != 0:
        return [], [], "sketch has an unbalanced opening brace"
    return lemmas, groups, None


#跟在这些符号/关键字后面的大括号是表达式(集合字面量)，不是证明体
_EXPRESSION_BEFORE_BRACE = set("=<>!+-*/%,(|&[")#表达式前缀非空白字符
_EXPRESSION_KEYWORDS = frozenset({"in", "set", "iset", "multiset", "map", "imap"})#表达式前缀单词
_TRAILING_WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_']*$")#字符串末尾满足格式的字符串(若字符串末尾不满足格式，则返回 None)


def _brace_role(source: str, start: int) -> str:#判断 { 开头的一段是真正的代填 hole 还是 expression(表达式)；start 为 { 索引
    """Tell a lemma's proof body apart from a brace that belongs to an expression."""
    if source.startswith("{:", start):#{:attribute} #"{:"开头为属性
        return "attribute"
    prefix = source[:start].rstrip()#从 source 开头取到(不包括) start(即 {) 并去除末尾空白字符(如：空格，\t，\n)
    if not prefix:#真正的待填 hole
        return "body"
    if prefix[-1] in _EXPRESSION_BEFORE_BRACE:#表达式
        return "expression"
    word = _TRAILING_WORD.search(prefix)
    if word and word.group(0) in _EXPRESSION_KEYWORDS:#表达式；group(0) 即为整个字符串，等价于 group()
        return "expression"
    return "body"#真正的待填 hole


def _lemma_bodies(sketch: str) -> tuple[list[str], str | None]:#返回所有 lemma(引理) 的证明体；若报错，则不返回并返回错误信息
    """Return every lemma body, delimited by matching braces instead of a regex.

    A flat regex cannot see nesting, so a body holding an ``if`` or ``forall``
    block used to be cut short and its holes then looked like they sat outside
    a lemma.  A lemma must also end with its body, which rules out a bodyless
    lemma -- that is an unproven assumption, not a proof.
    """
    lemmas, groups, error = _scan_declarations(sketch)
    if error:
        return [], error
    if not lemmas:
        return [], "sketch must declare at least one lemma"
    bodies: list[str] = []
    for position, lemma_start in enumerate(lemmas):
        end = lemmas[position + 1] if position + 1 < len(lemmas) else len(sketch)#确定该引理范围末尾(position 表示当前是第几个引理，从 0 开始算)
        owned = [#找出引理范围内的证明体(约定一个引理内有且仅有一个证明体)
            group
            for group in groups
            if lemma_start < group[0] < end
            and _brace_role(sketch, group[0]) == "body"
        ]
        if not owned:
            return [], "every lemma must have a proof body"
        start, stop = owned[-1]#start 是 { 自身的下标，stop 是 } 之后一位(元组解包，group 是 (int, int))
        if sketch[stop:end].strip():#格式约定：引理必须以证明体结尾，引理后面不能有非空白字符
            return [], "every lemma must end with its proof body"
        bodies.append(sketch[start + 1 : stop - 1])
    return bodies, None


_LEMMA_NAME = re.compile(r"\s*(?:\{[^{}]*\}\s*)*([A-Za-z_][A-Za-z0-9_']*)")


def _lemma_names(source: str) -> list[str]:#取出所有顶层引理的名字，用于查重名
    """Return the declared name of every top-level lemma, skipping attributes."""
    lemmas, _, error = _scan_declarations(source)
    if error:
        return []
    names: list[str] = []
    for position in lemmas:
        match = _LEMMA_NAME.match(source, position + len(_LEMMA_KEYWORD))
        if match:
            names.append(match.group(1))
    return names


def _holes_in_bodies(source: str) -> tuple[set[str], str | None]:#该片段里出现在引理体内的洞
    bodies, error = _lemma_bodies(source)
    if error:
        return set(), error
    return set(_HOLE.findall("\n".join(bodies))), None


def split_hole_response(text: str) -> tuple[str | None, str, str | None]:
    """Split one hole answer into its proof body and any new lemma declarations.

    The agreed shape is "body first, new lemmas after", so the first top-level
    ``lemma`` keyword is the boundary.  A leaf answer simply has no declaration
    part; an answer written the other way round fails the declaration check
    below with a message the model can act on.
    """
    candidate, error = extract_candidate(text, "dafny_body")
    if error or candidate is None:
        return None, "", error or "empty hole answer"
    lemmas, _, scan_error = _scan_declarations(candidate)
    if scan_error:
        return None, "", scan_error
    if not lemmas:
        return candidate, "", None
    return candidate[: lemmas[0]].strip(), candidate[lemmas[0] :].strip(), None


def plan_expansion(
    parent: str,
    body: str,
    declarations: str,
    *,
    depth: int,
    max_depth: int,
    max_children: int,
    room: int,
    used_holes: set[str],
    used_lemmas: set[str],
) -> tuple[list[str], str | None]:
    """Validate one sub-sketch and return the child holes it opens.

    ``room`` is how many holes the whole tree may still grow by.  Every failure
    is phrased as an instruction, because it is fed straight back to the model.
    """
    if depth >= max_depth:
        return [], (
            f"nesting depth {max_depth} is exhausted at hole {parent}; "
            "return a complete proof body with no HOLE_ marker"
        )
    if not body:
        return [], f"hole {parent} needs its own proof body before any new lemma"

    if declarations:
        bodies_error = _lemma_bodies(declarations)[1]
        if bodies_error:
            return [], bodies_error
        declared = _lemma_names(declarations)
        clash = sorted(set(declared) & used_lemmas)
        if clash:
            return [], f"lemma name(s) already declared: {', '.join(clash)}"
        duplicate = sorted({n for n in declared if declared.count(n) > 1})
        if duplicate:
            return [], f"duplicate lemma name(s): {', '.join(duplicate)}"
        outside, holes_error = _holes_in_bodies(declarations)
        if holes_error:
            return [], holes_error
        stray = sorted(set(_HOLE.findall(declarations)) - outside)
        if stray:
            return [], "hole markers must occur inside lemma bodies"

    children = list(dict.fromkeys(_HOLE.findall(body) + _HOLE.findall(declarations)))
    prefix = f"{parent}_"
    misnamed = sorted(n for n in children if not n.startswith(prefix) or n == prefix[:-1])
    if misnamed:
        return [], (
            f"a hole opened under {parent} must be named HOLE_{prefix}<suffix>; "
            f"rename: {', '.join(misnamed)}"
        )
    reused = sorted(set(children) & used_holes)
    if reused:
        return [], f"hole name(s) already in use: {', '.join(reused)}"
    if len(children) > max_children:
        return [], f"at most {max_children} new holes per expansion, got {len(children)}"
    if len(children) > room:
        return [], f"the proof may only grow by {room} more hole(s), got {len(children)}"
    return children, None


def parse_sketch(text: str, task: dict[str, Any]) -> tuple[str | None, list[str], str | None]:#解析 GLM 生成的草图    """Extract a safe sketch and its ordered, de-duplicated hole names."""
    sketch, error = extract_candidate(text, "dafny_body")
    if error or sketch is None:
        return None, [], error or "empty sketch"
    if _FORBIDDEN.search(sketch):
        return None, [], "sketch contains a forbidden declaration or trust escape"
    if "//" in sketch or "/*" in sketch or "*/" in sketch:#禁止注释(防止伪造有效 hole)
        return None, [], "comments are not allowed in a Sketch response"
    found = _HOLE.findall(sketch)
    lemma_bodies, body_error = _lemma_bodies(sketch)
    if body_error:#增加格式解析错误提前报错
        return None, [], body_error
    body_holes = _HOLE.findall("\n".join(lemma_bodies))
    if set(found) - set(body_holes):
        return None, [], "hole markers must occur inside lemma bodies"
    allowed = set(task.get("allowed_holes", []))
    if not found:
        return None, [], "sketch must contain at least one HOLE_<name> marker"
    unknown = sorted(set(found) - allowed) if allowed else []
    if unknown:
        return None, [], f"sketch contains unknown holes: {', '.join(unknown)}"
    holes = list(dict.fromkeys(found))#去重，保留首次出现的顺序
    minimum = int(task.get("min_holes", 1))
    maximum = int(task.get("max_holes", len(holes)))
    if len(holes) < minimum or len(holes) > maximum:#min_hole <= hole <= max_hole
        return None, [], f"sketch must contain between {minimum} and {maximum} holes"
    required = task.get("required_declarations", [])#hole 名称是否允许出现
    missing = [item for item in required if item not in sketch]#要包含任务要求的声明(有主证明，辅助引理的数量固定，证明结构固定)，目前未进一步验证深层结构(如各引理参数及类型，ensures，位置)
    if missing:
        return None, [], "sketch is missing required declaration(s)"
    return sketch, holes, None


def _fill_hole(rendered: str, name: str, body: str) -> str:#按整词替换单个 hole
    #str.replace 会让 HOLE_A 吃掉 HOLE_AB 的前缀，留下一段无意义的残码；
    #用词边界限定，并用 lambda 交付替换文本，避免 body 里的反斜杠被当成转义
    return re.sub(rf"\bHOLE_{re.escape(name)}\b", lambda _: body, rendered)


def assemble_sketch(#把 GLM 生成的草图放入固定 Dafny 模板
    task: dict[str, Any],
    project_dir: Path,
    sketch: str,
    fills: dict[str, str],
    *,
    internal_stubs: bool,
    allowed: set[str] | None = None,#嵌套时洞会长出来，白名单要跟着走
) -> str:
    """Insert a sketch into the fixed harness and fill holes safely."""
    template_path = project_dir / task["template_path"]
    template = template_path.read_text(encoding="utf-8")
    if "{{SKETCH}}" not in template:
        raise ValueError("Sketch template has no {{SKETCH}} placeholder")
    known = set(task.get("allowed_holes", [])) if allowed is None else allowed
    names = set(_HOLE.findall(sketch))
    if names - known:
        raise ValueError("sketch contains an unknown hole")
    rendered = sketch
    for name in names:
        if name in fills:
            body = fills[name]
            if _FORBIDDEN.search(body) or _HOLE.search(body):#不能引入不可信假设/留下未完成空洞
                raise ValueError(f"hole {name} contains a forbidden construct")
            rendered = _fill_hole(rendered, name, body)
        elif internal_stubs:#允许暂时占位
            rendered = _fill_hole(rendered, name, "assume {:axiom} false;")
        else:
            raise ValueError(f"hole {name} is unresolved")
    if not internal_stubs and (_HOLE.search(rendered) or _FORBIDDEN.search(rendered)):#最终组装时再次检查
        raise ValueError("final assembly contains an unresolved hole or trust escape")
    return template.replace("{{SKETCH}}", rendered)


def _record(result: VerificationResult) -> dict[str, Any]:
    return result.to_dict()


def _stage_status(result: VerificationResult | None, fallback: str) -> str:#细化报告：优先验证器本身报错
    """Report the underlying cause rather than hiding it behind a stage label."""
    if result is not None and result.status in _INFRASTRUCTURE_STATUSES:
        return result.status
    return fallback


def _hole_record(#实时 hole 快照，方便复盘失败
    name: str,
    status: str,
    candidate: str | None,
    result: VerificationResult | None,
    attempts: list[dict[str, Any]],#详细历史记录
) -> HoleRecord:
    """Snapshot one hole, including a hole abandoned mid-attempt."""
    return HoleRecord(
        name,
        status,
        candidate,
        len(attempts),
        _record(result) if result else None,
        attempts,
    )


def _hole_prompt(#下一轮提示词
    task: dict[str, Any],
    sketch: str,
    name: str,
    attempts: list[dict[str, Any]],
    *,
    depth: int = 1,
    may_nest: bool = False,
    max_children: int = 0,
    room: int = 0,
) -> str:
    """Build the next hole prompt, including the complete latest diagnosis."""
    prompt = (
        task["prompt"]
        + f"\nFill only the Dafny proof body for hole {name}.\n"
        + "Available helper declarations and the current sketch are:\n"
        + sketch
    )
    allowance = min(max_children, room)
    if may_nest and allowance > 0:#允许继续分解：说清格式和命名规则
        prompt += (
            f"\n\nHole {name} sits at nesting depth {depth}. You may either return"
            " its complete proof body, or decompose it: write the proof body"
            " first, then declare the new helper lemmas it calls below it."
            f" Each new proof hole must be named HOLE_{name}_<suffix> and sit"
            f" inside a lemma body; you may open at most {allowance} of them."
        )
    else:
        prompt += (
            f"\n\nHole {name} may not be decomposed any further; return a"
            " complete proof body containing no HOLE_ marker."
        )
    if not attempts:
        return prompt
    #如前面失败，追加提示词
    previous = attempts[-1]
    verification = previous.get("verification") or {}
    candidate = previous.get("candidate") or "<unparseable or empty output>"
    feedback = verification.get("feedback") or "<no verifier diagnostics>"
    prompt += (
        f"\n\nPrevious attempt (round {previous.get('round')}):\n{candidate}"
        f"\nPrevious verifier status: {verification.get('status', '<unknown>')}"
        f"\nComplete Dafny diagnostics from the previous attempt:\n{feedback}"
    )
    counterexample = verification.get("counterexample")
    if counterexample is not None:
        prompt += "\nCounterexample: " + json.dumps(counterexample, ensure_ascii=False)
    return prompt + "\nReturn a complete replacement proof body only."


def run_sketch(
    client: Generator,
    task: dict[str, Any],
    *,
    project_dir: Path,
) -> dict[str, Any]:
    """Run sketch, hole filling, and final verification/audit stages."""
    max_calls = _task_int(task, "max_calls", 12)#所有阶段总最多调用次数
    sketch_rounds = _task_int(task, "max_sketch_rounds", 3)
    hole_rounds = _task_int(task, "max_hole_rounds", 3)#每个 hole 最多尝试几轮
    timeout = _task_int(task, "timeout_seconds", 120)#每次 Dafny 的超时
    max_depth = _task_int(task, "max_hole_depth", 3)#1 表示不允许嵌套
    max_children = _task_int(task, "max_child_holes", 4)#单次展开最多开几个子洞
    max_total_holes = _task_int(task, "max_total_holes", 12)#整棵树的洞总数上限
    calls = 0
    started = time.monotonic()
    total_timeout = _task_int(task, "total_timeout_seconds", 600)
    sketch: str | None = None
    holes: list[str] = []
    sketch_records: list[dict[str, Any]] = []
    last_sketch_result: VerificationResult | None = None#最后一轮草图的验证结果(解析失败时为 None)

    def _remaining() -> float:#实时剩余时间，方便总超时判定、报错及退出
        return total_timeout - (time.monotonic() - started)

    def generate(prompt: str) -> str:#细化报错：统一用额度耗尽专用接口，差异化报错类型
        nonlocal calls
        if _remaining() <= 0:
            raise _BudgetExhausted("Sketch total time budget exhausted", TIMEOUT)
        if calls >= max_calls:
            raise _BudgetExhausted(
                "Sketch model-call budget exhausted", BUDGET_EXHAUSTED
            )
        calls += 1
        return client.generate(prompt)

    def dafny_timeout() -> int | None:#返回单次调用剩余时间，增加总时间不得超时逻辑
        """Shrink one Dafny call to what is left of the total budget.

        A single call must not be allowed to run for the full per-call timeout
        when the task only has a few seconds of its total budget left.
        """
        left = _remaining()
        if left < 1.0:
            return None
        return max(1, min(timeout, int(left)))

    #1.生成草图
    base_prompt = task["prompt"] + (
        "\nReturn only a Dafny proof sketch. Include the required helper lemma "
        "declarations and use HOLE_<name> as each proof body."
    )
    for round_number in range(1, sketch_rounds + 1):
        try:
            raw = generate(base_prompt if round_number == 1 else base_prompt + "\nPrevious diagnostics:\n" + sketch_records[-1]["feedback"])
        except _BudgetExhausted as exc:#细化超时&调用次数用尽报错
            return _failure(task, exc.status, str(exc), calls, sketch_records, [])
        except GLMClientError as exc:
            return _failure(task, API_ERROR, str(exc), calls, sketch_records, [])
        parsed, found, error = parse_sketch(raw, task)
        if error:
            last_sketch_result = None#本轮连解析都没过，之前那轮的验证结果不能代表现状
            sketch_records.append({"round": round_number, "status": SKETCH_FORMAT_ERROR, "feedback": error})
            continue
        assert parsed is not None
        try:
            source = assemble_sketch(task, project_dir, parsed, {}, internal_stubs=True)
        except (OSError, ValueError) as exc:
            return _failure(task, SKETCH_FORMAT_ERROR, str(exc), calls, sketch_records, [])
        budget = dafny_timeout()#增加总体超时判定：超时直接报错返回，不超时重新规划可用时间后调用
        if budget is None:
            return _failure(task, TIMEOUT, "Sketch total time budget exhausted", calls, sketch_records, [])
        verification = verify_dafny_source(source, timeout_seconds=budget, audit=False)
        last_sketch_result = verification
        sketch_records.append({"round": round_number, "status": verification.status, "feedback": verification.feedback})
        if verification.ok:
            sketch, holes = parsed, found
            break
        if verification.status == VERIFIER_ERROR:
            return _failure(task, verification.status, verification.feedback, calls, sketch_records, [])
    if sketch is None:
        #能解析但 Dafny 不通过是 REJECTED，只有解析失败才是 SKETCH_FORMAT_ERROR
        status = _stage_status(
            last_sketch_result, REJECTED if last_sketch_result else SKETCH_FORMAT_ERROR
        )
        return _failure(task, status, f"no verifying sketch within budget (last round: {status})", calls, sketch_records, [])

    #2，逐个填 hole；每个洞既可以直接写出证明体，也可以交回子草图继续分解
    fills: dict[str, str] = {}
    hole_records: list[HoleRecord] = []
    allowed: set[str] = set(task.get("allowed_holes", [])) | set(holes)
    seen_holes: set[str] = set(holes)#全树用过的洞名，禁止重复
    reserved_lemmas = set(_lemma_names(sketch))#harness 里的引理也不能被重名覆盖
    try:
        reserved_lemmas |= set(
            _lemma_names((project_dir / task["template_path"]).read_text(encoding="utf-8"))
        )
    except OSError as exc:
        return _failure(task, SKETCH_FORMAT_ERROR, str(exc), calls, sketch_records, [])
    pending: list[tuple[str, int, str | None]] = [
        (name, 1, None) for name in reversed(holes)
    ]#栈：深度优先，子树做完再回到兄弟节点

    while pending:
        name, depth, parent = pending.pop()
        last_candidate: str | None = None
        last_result: VerificationResult | None = None
        status = HOLE_FAILED
        kind = "leaf"
        children: list[str] = []
        attempts: list[dict[str, Any]] = []
        room = max_total_holes - len(seen_holes)
        may_nest = depth < max_depth

        def snapshot(state: str) -> HoleRecord:
            record = _hole_record(name, state, last_candidate, last_result, attempts)
            record.depth, record.parent, record.kind = depth, parent, kind
            record.children = list(children)
            return record

        for round_number in range(1, hole_rounds + 1):
            try:
                raw = generate(
                    _hole_prompt(
                        task, sketch, name, attempts,
                        depth=depth, may_nest=may_nest,
                        max_children=max_children, room=room,
                    )
                )
            except (_BudgetExhausted, GLMClientError) as exc:#细化报错，同时记录 hole 错误快照(方便模型复盘)
                #预算或 API 中断也要留下当前 hole 的记录，否则无法复现失败点
                aborted = exc.status if isinstance(exc, _BudgetExhausted) else API_ERROR
                hole_records.append(snapshot(aborted))
                return _failure(task, aborted, str(exc), calls, sketch_records, hole_records)

            body, declarations, error = split_hole_response(raw)
            if error or body is None:
                last_result = VerificationResult(FORMAT_ERROR, False, error or "empty hole answer")
                attempts.append({"round": round_number, "candidate": None, "verification": _record(last_result)})
                continue
            candidate = f"{body}\n{declarations}".strip() if declarations else body
            if _FORBIDDEN.search(candidate):
                last_result = VerificationResult(FORMAT_ERROR, False, "hole contains a forbidden construct")
                attempts.append({"round": round_number, "candidate": candidate, "verification": _record(last_result)})
                continue
            if "//" in candidate or "/*" in candidate or "*/" in candidate:#注释可用来伪造 hole 标记
                last_result = VerificationResult(FORMAT_ERROR, False, "comments are not allowed in a hole answer")
                attempts.append({"round": round_number, "candidate": candidate, "verification": _record(last_result)})
                continue

            opened = list(dict.fromkeys(_HOLE.findall(body) + _HOLE.findall(declarations)))
            nesting = bool(declarations or opened)
            if nesting:#子草图：先校验命名/数量/深度，再看结构能不能验证
                children, plan_error = plan_expansion(
                    name, body, declarations,
                    depth=depth, max_depth=max_depth, max_children=max_children,
                    room=room, used_holes=seen_holes, used_lemmas=reserved_lemmas,
                )
                if plan_error:
                    children = []
                    last_result = VerificationResult(FORMAT_ERROR, False, plan_error)
                    attempts.append({"round": round_number, "candidate": candidate, "verification": _record(last_result)})
                    continue
                grown = _fill_hole(sketch, name, body)
                if declarations:
                    grown = grown.rstrip() + "\n" + declarations
                structure_error = _lemma_bodies(grown)[1]
                if structure_error is None:
                    stray = set(_HOLE.findall(grown)) - _holes_in_bodies(grown)[0]
                    structure_error = "hole markers must occur inside lemma bodies" if stray else None
                if structure_error:#组合出来的整体结构必须仍然合法
                    children = []
                    last_result = VerificationResult(FORMAT_ERROR, False, structure_error)
                    attempts.append({"round": round_number, "candidate": candidate, "verification": _record(last_result)})
                    continue
                trial, trial_fills = grown, {}
            else:
                grown, trial, trial_fills = sketch, sketch, {name: body}

            last_candidate = candidate
            try:
                # Validate each hole against declarations and internal stubs;
                # previously filled bodies are not trusted as proof context.
                source = assemble_sketch(
                    task, project_dir, trial, trial_fills,
                    internal_stubs=True, allowed=allowed | set(children),
                )
            except (OSError, ValueError) as exc:
                children = []
                last_result = VerificationResult(FORMAT_ERROR, False, str(exc))
                attempts.append({"round": round_number, "candidate": candidate, "verification": _record(last_result)})
                continue
            budget = dafny_timeout()
            if budget is None:#记录 hole 错误快照(方便模型复盘)，同时提前报错返回
                hole_records.append(snapshot(TIMEOUT))
                return _failure(task, TIMEOUT, "Sketch total time budget exhausted", calls, sketch_records, hole_records)
            last_result = verify_dafny_source(source, timeout_seconds=budget, audit=False)
            attempts.append({"round": round_number, "candidate": candidate, "verification": _record(last_result)})
            if last_result.ok:
                if nesting:#结构验证通过才提交，失败的声明不会污染 sketch
                    sketch = grown
                    allowed |= set(children)
                    seen_holes |= set(children)
                    reserved_lemmas |= set(_lemma_names(declarations))
                    pending.extend(
                        (child, depth + 1, name) for child in reversed(children)
                    )
                    kind = "expanded"
                else:
                    fills[name] = body
                status = VERIFIED
                break
            children = []
            if last_result.status == VERIFIER_ERROR:#验证器本身坏了，重试没有意义，提前返回
                break

        if status != VERIFIED:
            status = _stage_status(last_result, HOLE_FAILED)
        hole_records.append(snapshot(status))#hole 无论正误都记录快照
        if status != VERIFIED:#记录完之后，若错误，再报错返回
            reason = (
                f"hole {name} failed within budget"
                if status == HOLE_FAILED
                else f"hole {name} stopped with {status}"
            )
            return _failure(task, status, reason, calls, sketch_records, hole_records)

    #3.最终组装(所有 hole verified 后才执行)；嵌套展开在这一步塌成一个平面程序
    try:
        final_source = assemble_sketch(
            task, project_dir, sketch, fills, internal_stubs=False, allowed=allowed
        )
    except (OSError, ValueError) as exc:
        return _failure(task, ASSEMBLY_ERROR, str(exc), calls, sketch_records, hole_records)
    budget = dafny_timeout()
    if budget is None:#细化报错
        return _failure(task, TIMEOUT, "Sketch total time budget exhausted", calls, sketch_records, hole_records)
    verified = verify_dafny_source(final_source, timeout_seconds=budget, audit=False)
    if not verified.ok:#细化报错
        #超时或验证器故障不是"组装出来的程序证不出来"，不要压成 ASSEMBLY_ERROR
        return _failure(task, _stage_status(verified, ASSEMBLY_ERROR), verified.feedback, calls, sketch_records, hole_records)
    budget = dafny_timeout()
    if budget is None:
        return _failure(task, TIMEOUT, "Sketch total time budget exhausted", calls, sketch_records, hole_records)
    #只跑 audit：verify 刚刚单独跑过，再用 verify_dafny_source(audit=True) 会白验一遍
    audited = audit_dafny_source(final_source, timeout_seconds=budget)
    if not audited.ok:#细化报错
        #同理：只有真的查出信任逃逸才算 AUDIT_REJECTED
        return _failure(task, _stage_status(audited, AUDIT_REJECTED), audited.feedback, calls, sketch_records, hole_records)
    return {
        "task_id": task["id"], "success": True, "final_status": VERIFIED,
        "stop_reason": "verified", "model_calls": calls,
        "sketch_rounds": sketch_records,
        "sketch": sketch,#展开完成后的结构，含所有子草图
        "holes": [asdict(item) for item in hole_records],
        "final_verification": _record(verified), "final_audit": _record(audited),
        "final_program": final_source,
    }


def _failure(task: dict[str, Any], status: str, feedback: str, calls: int, sketches: list[dict[str, Any]], holes: list[Any]) -> dict[str, Any]:
    return {"task_id": task["id"], "success": False, "final_status": status, "stop_reason": status.lower(), "feedback": feedback, "model_calls": calls, "sketch_rounds": sketches, "holes": [asdict(h) if isinstance(h, HoleRecord) else h for h in holes]}


def main() -> int:
    parser = argparse.ArgumentParser(description="Run a three-stage Dafny Sketch task")
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--tasks", type=Path, default=Path(__file__).parent / "tasks" / "formal_tasks.json")
    args = parser.parse_args()
    try:
        tasks = json.loads(args.tasks.read_text(encoding="utf-8"))
        task = next(item for item in tasks if item["id"] == args.task_id)
        if task.get("verifier") != "dafny_sketch":
            raise ValueError("selected task is not a dafny_sketch task")
        from glm_client import GLMClient
        result = run_sketch(GLMClient(), task, project_dir=args.tasks.parent.parent)
    except (OSError, StopIteration, KeyError, ValueError, GLMClientError) as exc:
        print(json.dumps({"status": "CONFIG_ERROR", "error": str(exc)}, ensure_ascii=False))
        return 2
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result["success"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
#finish review：2026.9.14
#finish review version-"2.增加块结构解析器，同时要求每个 lemma 必须以证明体结尾；3.区分最终错误状态；4.增加 Sketch 总超时限制，同时剩余不足 1 秒不再启动新的验证；5.Sketch 中断时先补齐当前 hole 的记录再报错返回" 2026.9.21