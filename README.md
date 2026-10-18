# GLM 5.3 Highspeed + Deterministic Verifiers

本项目通过 GLM 的 Anthropic-compatible Messages API 调用
`glm-5.3-highspeed`，将模型输出交给 Z3 或 Dafny 等确定性验证器。判分权只在
验证器，不依赖另一个 LLM 充当裁判。模型不能修改规格、harness、后置条件或
验证脚本，只能输出验证器要求的候选表达式、方法体或证明体。

三种运行逻辑：

1. `direct`：模型只生成一次，验证器结果直接作为测试结果。
2. `feedback`：验证失败后，把错误信息或反例反馈给模型，循环至验证通过
   或达到强制停止条件。
3. `sketch`：针对较复杂的 Dafny 证明，先生成证明草图，再逐个填充证明空洞，
   最后组装成无信任逃逸的完整程序并审计。填空洞时还可以继续交回子草图，
   把一个洞递归地分解下去。

## 目录结构

```text
glm_client.py                 GLM Anthropic-compatible API 客户端
verifiers.py                  验证器注册表、Z3/Dafny 适配器和候选提取逻辑
runner.py                     direct/feedback 两种运行模式
sketch_runner.py              Sketch 三阶段流程和 Dafny 草图解析器
screen_data.py                确定性可验证数据筛选脚本
tasks/formal_tasks.json       固定规格任务定义
tasks/dafny/*.dfy             不允许模型修改的 Dafny 验证模板
tests/test_core.py            客户端、注册表、direct/feedback 单元测试
tests/test_sketch.py          草图解析、三阶段流程、预算和状态单元测试
tools/dafny-4.11.0/           随项目携带的 Dafny 发行版(查找链的最后一级)
requirements.txt              Python 依赖
```

## 环境准备

不要求创建虚拟环境，直接在当前 Python 环境安装依赖：

```powershell
python -m pip install -r requirements.txt
```

Dafny 的查找顺序是 `DAFNY_BIN` 环境变量 → `PATH` 中的 `dafny` →
`tools/dafny-4.11.0/dafny/Dafny.exe`。要指定其他版本：

```powershell
$env:DAFNY_BIN = "D:\path\to\Dafny.exe"
```

## GLM 配置

推荐使用环境变量：

```powershell
$env:GLM_API_KEY = "your-api-key"
$env:GLM_BASE_URL = "https://api-gateway.glm.ai"
$env:GLM_MODEL = "glm-5.3-highspeed"
```

也可以在项目根目录建立 `api_key.md`，其中只保存密钥或包含
`Authorization: Bearer ...` 的 curl 示例。该文件已被 `.gitignore` 排除，
提交时不要包含真实密钥。

其余可选变量：`GLM_MAX_TOKENS`(默认 4096)、`GLM_TIMEOUT_SECONDS`(180)、
`GLM_MAX_RETRIES`(3)、`GLM_RETRY_DELAY_SECONDS`(1)。超时、网络故障、
HTTP 408/425/429/5xx、非 JSON 响应和空文本都会重试，重试用尽后抛出
`GLMClientError`，错误信息不包含密钥。

## 使用方法

查看任务：

```powershell
python runner.py --list
```

直接验证：

```powershell
python runner.py --mode direct --task-id z3_abs
```

验证反馈循环，最多调用模型三次：

```powershell
python runner.py --mode feedback --max-rounds 3 --task-id z3_max3
```

运行 Dafny 任务：

```powershell
python runner.py --mode feedback --max-rounds 3 --task-id dafny_abs_body
```

保存结果：

```powershell
python runner.py --mode direct --task-id z3_abs --output results/run.json
```

运行 Sketch 任务(独立 runner，不走 `runner.py`)：

```powershell
python sketch_runner.py --task-id dafny_sketch_nonnegative
python sketch_runner.py --task-id dafny_sketch_sum_formula   # 允许嵌套分解
```

退出码：`0` 全部成功，`1` 至少一个任务失败，`2` 配置或输入错误。

## 任务定义

`tasks/formal_tasks.json` 是一个任务数组，公共字段：

```text
id                任务唯一标识
name              人类可读名称
verifier          z3 | dafny | dafny_sketch
output_format     z3_expression | dafny_body | dafny_sketch
prompt            交给模型的任务说明
timeout_seconds   单次验证器调用的超时
```

按验证器追加的字段：

```text
z3            spec                   已注册的规格名(单规格任务)
              specs                  规格名列表(多规格任务，全部成立才通过)
dafny         template_path          含 {{CANDIDATE}} 占位符的固定模板
              audit                  是否执行 dafny audit(默认 true)
dafny_sketch  template_path          含 {{SKETCH}} 占位符的固定 harness
              allowed_holes          根草图允许出现的 hole 名称白名单
              required_declarations  必须出现的声明字符串
              min_holes/max_holes    根草图的 hole 数量上下限
              max_hole_depth         嵌套层数上限(根草图算第 1 层，1 = 不许嵌套)
              max_child_holes        单次展开最多开几个子洞
              max_total_holes        整棵 hole 树的洞总数上限
              max_sketch_rounds      草图阶段的重试轮数
              max_hole_rounds        单个 hole 的重试轮数
              max_calls              三阶段合计的模型调用上限
              total_timeout_seconds  整个任务的总时间上限
```

`specs` 存在时优先于 `spec`。模板由本项目提供，模型看不到也不能修改。
`verifiers.py` 会拒绝没有占位符的模板，`runner.py` 会拒绝缺字段或 id 重复的
任务文件。

## direct 与 feedback

```text
读取任务 → 调用 GLM → 提取候选 → 交给验证器 → 得到结果
                                                  │
             direct: 直接作为本次测试结果 ←────────┤
                                                  │
             feedback: 通过则结束；失败则把诊断和反例
                       喂回 GLM 重新生成，直到通过或触发停止条件
```

候选提取会先去掉 `<think>` 区块，再取最后一个 Markdown 代码块；
`z3_expression` 要求结果恰好是一行表达式，只允许整数字面量、`x`、
`+ - *`、括号、比较和 `If(cond, a, b)`（AST 白名单，不允许除法和其他函数）。

多规格任务（`specs`）中每条规格单独判定，全部通过才算 `VERIFIED`；任意一条
被推翻即 `REJECTED`，反馈里会逐条列出状态和反例，详见 "Z3 规格"。

feedback 模式的强制停止条件：

- 达到 `--max-rounds` 轮数上限；
- GLM 调用失败(`API_ERROR`)；
- 验证器本身故障(`VERIFIER_ERROR`)。

`TIMEOUT` 和 `UNKNOWN` 视为瞬时状态，会用掉剩余轮数继续重试。

## 验证状态

通用状态：

```text
VERIFIED        验证通过
REJECTED        验证失败(含 Dafny audit 不干净)
FORMAT_ERROR    模型输出无法转换为验证器输入
TIMEOUT         模型或验证器超时
UNKNOWN         验证器无法判定(如 Z3 返回 unknown)
API_ERROR       GLM 调用失败
VERIFIER_ERROR  验证器缺失、配置错误或规格未注册
```

Sketch 追加：

```text
SKETCH_FORMAT_ERROR  草图无法解析
HOLE_FAILED          某个证明空洞在预算内未通过
ASSEMBLY_ERROR       组装后的完整程序无法验证
AUDIT_REJECTED       完整验证通过但审计发现信任依赖
BUDGET_EXHAUSTED     模型调用次数用尽(时间用尽报 TIMEOUT)
```

阶段状态只描述"模型没做到"。若底层原因是 `TIMEOUT`、`UNKNOWN` 或
`VERIFIER_ERROR`，最终状态直接透传底层原因，不会被包装成 `HOLE_FAILED`、
`ASSEMBLY_ERROR` 或 `AUDIT_REJECTED`——这样 `AUDIT_REJECTED` 才始终意味着
"真的查出了信任逃逸"这一最需要人工关注的信号。草图阶段同理：能解析但
Dafny 不通过时报 `REJECTED`，只有解析失败才报 `SKETCH_FORMAT_ERROR`。

## Sketch 证明分解

### 阶段一：生成并验证草图

调用 GLM 生成主引理和辅助引理的**声明**，每个待填证明体写成 `HOLE_<name>`。
`sketch_runner.py` 用逐字符的块结构解析器校验草图：跟踪大括号深度、跳过
字符串与字符字面量（区分 Dafny 标识符里的撇号，如 `n'`）、把签名里的集合
字面量和 `{:attribute}` 与真正的证明体区分开。校验规则：

- 禁止 `assume`、`axiom`、`extern`、`include`、`module`、`method`、
  `function`，以及 `{:axiom}`、`{:verify false}`、`{:only}`、`{:nowarn}`、
  `{:timeLimit}`、`{:rlimit}` 这类会跳过验证、缩小验证范围或自行放大验证
  开销的属性（`{:induction}`、`{:trigger}` 等不影响判定的属性仍可使用）；
- 禁止注释（注释可用来伪造 hole 标记）；
- 每个 `lemma` 必须有证明体且以证明体结尾（无体 lemma 等于一条未经证明的
  假设）；
- 所有 hole 标记必须出现在 lemma 证明体内；
- hole 名称必须在 `allowed_holes` 内，数量在 `min_holes`~`max_holes` 之间；
- `required_declarations` 列出的声明必须出现。

草图连同内部占位实现（`assume {:axiom} false;`，只能由 runner 注入）一起送去
Dafny 验证结构是否成立；失败则把诊断反馈给 GLM 重新生成。

### 阶段二：逐个填充证明空洞

按草图中首次出现的顺序处理每个 hole：只把当前 hole 填入候选，**其余 hole
仍用占位实现**——已填好的证明体不作为可信上下文，避免 hole 之间互相借用
结论。每个 hole 独立记录候选、轮次、耗时和验证输出。失败时把完整 Dafny
诊断和反例反馈给 GLM，按该 hole 的重试预算继续；预算内仍失败则终止任务。
遇到 `VERIFIER_ERROR` 立即终止，不做无意义的重试。

### 嵌套：一个 hole 可以再是一个 sketch

`max_hole_depth > 1` 时，模型填某个 hole 可以不直接写出证明体，而是交回一个
**子草图**：先写这个 hole 自己的证明体，再在下面声明它调用的新辅助引理，
新引理的证明体继续留成 `HOLE_*`。运行器递归地把这些子洞排进队列。

响应格式不引入新语法，就按"体在前、新引理在后"切分（第一个顶层 `lemma`
关键字是分界）。没有新引理也没有新洞的回答就是叶子，照旧处理。

```dafny
if n == 0 { } else { MainProof(n - 1); Step(n); }   // 本 hole 的证明体
lemma Step(n: nat) requires n > 0                   // 新声明的辅助引理
  requires Sum(n - 1) * 2 == (n - 1) * n
  ensures Sum(n) * 2 == n * (n + 1)
{ HOLE_Main_step }                                  // 新的子洞
```

约束：

- 子洞必须命名为 `HOLE_<父洞名>_<后缀>`，于是树形归属从名字直接可读
  （`Main` → `Main_step` → `Main_step_unfold`），根任务的 `allowed_holes`
  仍然是有效锚点；
- 新引理名不得与 harness 或已有草图中的引理重名；
- 新洞必须落在引理体内，禁止注释和全部信任逃逸构造，规则与根草图一致；
- 受 `max_hole_depth`、`max_child_holes`、`max_total_holes` 三重约束，
  再加上 `max_calls` 和 `total_timeout_seconds` 兜底，递归必然终止；
- 深度用尽时提示词会明确要求"返回不含 `HOLE_` 的完整证明体"。

展开先按上述规则校验，再把"填入证明体 + 追加新声明"后的整体结构送去 Dafny
（所有未填的洞仍打占位）验证；**只有结构验证通过才提交**，被拒的展开不会把
声明留在草图里。每条 hole 记录带 `depth`、`parent`、`kind`（leaf/expanded）
和 `children`，结果里的 `sketch` 字段是展开完成后的完整结构。

处理顺序是深度优先：一个子树做完才回到它的兄弟节点。

### 阶段三：组装、完整验证和审计

所有 hole 都 `VERIFIED` 后，才无占位组装完整程序（嵌套展开在这一步塌成一个
平面 Dafny 程序），并再次检查不存在未替换的 hole 和任何禁止构造，然后执行
一次完整 `dafny verify`，通过后再单独执行一次 `dafny audit`
（`audit_dafny_source`，不重复验证）。两步各自保留状态和时间预算：验证失败是
`ASSEMBLY_ERROR`，审计不干净是 `AUDIT_REJECTED`。审计发现任何信任依赖时最终
状态必须是失败，不能报告成功。

一次成功的三洞扁平任务合计 6 次 Dafny 调用：草图 1 次、每个 hole 1 次、最终
`verify` 1 次、最终 `audit` 1 次。嵌套时每次展开也各占 1 次结构验证。

任务成功的必要条件是：所有 hole 都已填充、完整验证通过、最终审计通过。

### 预算控制

- `max_calls`：三阶段合计的模型调用上限，用尽报 `BUDGET_EXHAUSTED`；
- `total_timeout_seconds`：任务总时间，用尽报 `TIMEOUT`；
- 单次 Dafny 调用的超时取 `min(timeout_seconds, 剩余总时间)`，剩余不足
  1 秒时不再启动新的验证；
- `verify_dafny_source(audit=True)`（direct/feedback 的 Dafny 路径）中，
  `timeout_seconds` 是整次调用的上界：audit 阶段只使用 verify 阶段之后剩下
  的时间，两个子进程不会各用满一份；
- 任一阶段中断（API 失败、预算耗尽、超时）都会先为当前正在处理的 hole 补一
  条记录，保留已有的候选和诊断，再报错返回。

输出包含最终状态、停止原因、模型调用次数、草图各轮记录、各 hole 的完整记录、
验证诊断、审计诊断和最终程序。

## Z3 规格

规格是对"输出 y 与输入 x 的关系"的声明式约束，不是参考实现。完整函数规格
对每个 x 唯一确定 y；性质规格只约束一个方面，适合用 `specs` 组合出更严的要求。

```text
完整函数规格  abs relu double max3 negate successor square min_zero
              sign clamp_0_10
性质规格      nonneg nonpos even ge_x le_x magnitude_x bounded_1 bounded_10
```

`registered_z3_specs()` 返回当前列表。任务既可以只要一条完整函数规格
（`spec`），也可以用 `specs` 同时要求若干条性质——**每条单独求解、单独判定，
全部成立才算通过**，失败时模型能看出坏在哪条性质上：

```text
abs: REJECTED — counterexample: x=-1, candidate=-1, expected=1
nonneg: REJECTED — counterexample: x=-1, candidate=-1, expected=0
ge_x: VERIFIED
magnitude_x: VERIFIED
```

结果的 `details["specs"]` 里是逐条状态、诊断和反例；顶层 `counterexample`
取第一条被推翻的规格的反例，`feedback` 是上面那几行。聚合优先级是
`VERIFIER_ERROR > REJECTED > UNKNOWN > VERIFIED`——注册表出问题要先报出来，
不能被"模型答错"盖过去。

`check_z3_specs()` 是注册表自检：抽样确认每条规格在若干输入上都存在合法输出，
避免写出一条永远无法满足、导致任何回答都被判 `REJECTED` 的规格。测试里会运行。

## 扩展验证器

`verifiers.py` 用注册表分发，新增后端不必修改 `verify_candidate`：

```python
from verifiers import register_verifier, register_z3_spec

register_verifier("my_checker", my_adapter)          # adapter(task, candidate, project_dir)
register_z3_spec("triple", lambda z3, x, y: y == 3 * x)
```

`_VERIFIERS` 的键对应任务的 `verifier` 字段（接入新后端），`_Z3_SPECS` 的键
对应 `spec`/`specs` 字段（在 Z3 后端里加新规格）。规格函数签名是
`spec(z3, x, y)`——z3 是惰性导入的，模块由调用方注入。重名注册会抛
`ValueError`，避免验证依据被静默替换。任务文件里 `verifier` 不是字符串时返回
`VERIFIER_ERROR`，不会抛异常。

查询接口：

```text
registered_verifiers()        已注册的验证器后端
registered_z3_specs()         已注册的 Z3 规格
check_z3_specs()              抽样自检每条规格是否存在合法输出
```

Dafny 侧对外提供三个入口：

```text
verify_dafny(template_path, candidate, ...)   填模板后验证(direct/feedback)
verify_dafny_source(program, ..., audit)      验证整段源码，可选顺带审计
audit_dafny_source(program, ...)              只审计已经验证过的程序
```

## 数据筛选

默认检查相邻 `glm-simple-evals-main/data` 数据目录：

```powershell
python screen_data.py
```

也可以指定其他数据目录：

```powershell
python screen_data.py D:\path\to\data
```

筛选器只接受：

- 带形式化规格、验证器或 harness 的任务；
- 同时包含结构化代码和确定性测试的任务。

纯自然语言问答、只给最终答案或需要另一个 LLM 裁判的任务会被排除。

## 测试

```powershell
python -m unittest discover -s tests -v
```

需要 z3-solver 的用例在未安装时自动跳过；Sketch 的端到端用例会真实调用
Dafny。

## 已知限制

- `required_declarations` 只做字符串包含检查，不校验引理的参数类型、
  `ensures` 内容和位置。
- 禁止列表是按已知的逃逸手段逐条列举的，不是白名单。Dafny 默认把"这里有
  未经证明的假设"一类告警视为错误（`--allow-axioms`、`--allow-warnings` 都
  默认关闭），这层保护不要关掉。
- 阶段二用占位实现校验单个 hole，所以 hole 能引用其他引理的 `ensures` 而不
  依赖其证明体；hole 全部通过后仍可能在阶段三因终止性、`decreases` 等整体
  性质失败，这种情况报 `ASSEMBLY_ERROR`。
- 嵌套展开一经结构验证通过就固化进草图，不会因为子洞后来填不上而回溯重来；
  子洞用尽预算仍失败时整个任务按 `HOLE_FAILED` 停止。
- `max_hole_depth` 默认 3，即新写的 sketch 任务默认允许嵌套。要保持旧的扁平
  行为，在任务里显式写 `"max_hole_depth": 1`（`dafny_sketch_nonnegative`
  就是这样钉住的）。
- 多规格任务（`specs`）里每条规格各跑一次求解器，没有基于规格间蕴含关系的
  剪枝——规格条数多时求解次数线性增长。
</content>
</invoke>
