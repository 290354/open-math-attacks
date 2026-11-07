# 2026-11-07 · Erdős–Straus 猜想（4/n 的三项单位分分解）：无穷剩余类的 Lean 形式化 + 精确计算核查

> **结论级别：L2（部分形式化）** —— 由 CI 哨兵判定（`BUILD_OK` + `INCOMPLETE`，主命题留有显式 `sorry`）。
> 主命题本身未闭合；本 round 无缺口地形式化了三条无穷剩余类的显式解、提升引理与类覆盖定理，
> 并以可复现脚本核查了 2 ≤ n ≤ 10000 的全部情形。

## 一、问题

**Erdős–Straus 猜想**（Erdős & Straus, 1948）：对每个整数 n ≥ 2，方程

  4/n = 1/x + 1/y + 1/z

是否存在正整数解 (x, y, z)？等价整式形式：4xyz = n(xy + xz + yz)。
收录于 [Wikipedia 未解数学问题列表](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)（数论部分）与
[erdosproblems.com #242](https://www.erdosproblems.com/242)。

## 二、选题理由（为何是它而不是别的 open 问题）

1. **陈述一行且初等**，纯自然数算术——可用 **Lean core（无 Mathlib）完整写出**，满足本轮加权条件；
   大多数 open 问题（如需要序结构、拓扑、表示论的）连陈述都无法用 core 表达，形式化只能停 L0。
2. **参数有限、可穷举**：固定 n 后 (x,y,z) 的搜索空间可被初等不等式夹逼（x ∈ (n/4, 3n/4]）。
3. **部分结果极多、方法路径清晰**：已验证至 10^17（Salez 2014，附 C++ 代码）、10^18（Mihnea & Dumitru 2025 预印本）；
   Mordell 型模恒等式覆盖 mod 840 中除 1, 49, 121, 169, 289, 361 外全部剩余类；Terzi 推进到 mod 120120 的 198 类；
   Vaughan (1970) 给出例外计数上界 N·exp(−c(log N)^{2/3})。
4. **近年有同类推进先例**：社区明确把「覆盖恒等式的 Lean 形式化」「到素数的归约的形式化」列为有效贡献
   （见 cairn-commons 对该问题的 progress 说明），本 round 的产出正好落在这两类有效贡献之内。

## 三、可行性预判（动手前写定）

- 现状：猜想开放；计算验证 10^17/10^18；难类集中于 n ≡ 1 (mod 4)（配合不被 3 整除等进一步过滤）。
- 已知最好结果：如上；到素数的归约（4/n 有解 ⟹ 4/(mn) 有解）是文献标准事实。
- 本轮方法：(a) 用 Lean core 形式化三条无穷类的显式 witness + 提升引理 + 类覆盖定理；
  (b) Python 精确有理数搜索核查小范围难类。
- 预期能达到的程度：**不可能闭合猜想**（10^18 的计算墙 + 80 年数学史）。预期产出为
  「L2：关键引理零缺口、主命题留缺」——这正是实际得到的结果。

## 四、本轮做了什么

### 4.1 Lean 形式化（`lean/`，core-only，无 Mathlib）

| 结果 | 内容 | 状态 |
|---|---|---|
| `es_even` | n = 2m：4/n = 1/m + 1/(2m) + 1/(2m) | 零缺口 |
| `es_three_mod_four` | n = 4m+3：4/n = 1/(m+1) + 1/(2(m+1)n) + 1/(2(m+1)n) | 零缺口 |
| `es_three_div` | n = 3k：4/n = 1/k + 1/(6k) + 1/(6k) | 零缺口 |
| `es_lift` | n 可解 ⟹ k·n 可解（分母同乘 k）⇒ 反例最小者必为素数 | 零缺口 |
| `es_classes` | 三类并集上的覆盖定理 | 零缺口 |
| `es_five` | 数值样例 4/5 = 1/2 + 1/4 + 1/20（难类） | 零缺口 |
| `erdos_straus_conjecture` | **主命题，`sorry` 显式留缺** | 未闭合（诚实标注） |

### 4.2 计算核查（`scripts/erdos_straus_search.py`）

```
python3 scripts/erdos_straus_search.py 10000
# OK: 2 <= n <= 10000 全部通过（含 1666 个难类 n，全部找到并校验）
# 难类样例证书（n: (x,y,z)）: {5: (2,4,20), 13: (4,18,468), 17: (5,30,510), 25: (7,60,2100), 29: (8,78,9048)}
```

搜索不做任何未证假设：难类 n 用精确整数算术枚举（x ∈ (n/4, 3n/4]，对每个 x 把
1/y + 1/z = (4x−n)/(nx) 化为最简分数 a/b 后在 (b/a, 2b/a] 内枚举 y），
每个解回代整式方程校验。显式类 witness 与 Lean 中完全一致。

## 五、级别及依据（由 CI 哨兵决定，非主观）

- CI 工作流：`.github/workflows/lean-verify.yml`（push 触发，构建全部 `*/lean` 工程）。
- 本轮级别：**L2 = 部分形式化**。依据：`BUILD_OK`（工程编译通过）且 `INCOMPLETE`
  （`erdos_straus_conjecture` 使用 `sorry`）。未新增任何 `axiom`，未用 `native_decide`。
- 按 [open-math-attacks README](https://github.com/290354/open-math-attacks) 的分级表，
  L2 允许的措辞是「部分形式化」；标题/摘要不使用「证明/解决」等词。

## 六、失败与局限分析

1. **主命题不可达**：10^18 计算墙 + Elsholtz–Tao 对解数的 polylog 上界表明「数解数」路线
   难以直接给出存在性；本轮不假装接近。
2. **未形式化到素数的完整归约**：`es_lift` 给出「n 可解 ⟹ kn 可解」，但「每个 n ≥ 2 有素因子、
   故只需查素数」需要核心算术基本定理 API（core 内不便），本轮未做；此为下一轮候选。
3. **难类显式恒等式未新增**：Mordell mod 840 覆盖比本轮三条类强得多；本轮价值在于
   把一部分标准事实变成机器核查的、可复用的 core-only 形式化资产。
4. 若 CI 判 `BUILD_FAIL`，级别将如实降为 L1 并保留失败记录（不删历史）。

## 七、复现步骤

```bash
git clone https://github.com/290354/open-math-attacks.git
cd open-math-attacks/2026-11-07-erdos-straus-4n

# 计算核查（约 25s）
python3 scripts/erdos_straus_search.py 10000

# Lean 形式化（需 elan / Lean v4.35.0；或直接看仓库 CI 日志）
cd lean && lake build
# 期待：编译通过；唯一未完成证明为 erdos_straus_conjecture 的显式 sorry
```

## 八、下一轮建议

1. 形式化「归约到素数」全链：用 `Nat.minFac`（core 自带）证明每个 n ≥ 2 有素因子，
   把主命题的缺口压缩到「素数情形」。
2. 增加 n ≡ 2 (mod 3)、n ≡ 5 (mod 8) 等显式类（各自 witness 需先人工推导验证），
   把 `es_classes` 的覆盖面推向 mod 24 全部非 1 类。
3. 若要挑战难类，可形式化 Elsholtz–Tao 型模恒等式生成器（4acd − 1 分解），
   但注意其组合搜索部分超出 core 舒适区。

## 参考文献

1. P. Erdős, E. G. Straus（1948，问题提出；见 R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer, 2004, Problem D11）。
2. R. C. Vaughan, "On a problem of Erdős, Straus and Schinzel", *Proc. London Math. Soc.* (3) 21 (1970)——例外计数上界。
3. C. Elsholtz, T. Tao, "Counting the number of solutions to the Erdős–Straus equation on unit fractions", *J. Aust. Math. Soc.* 94 (2013)——素数上平均解数的 polylog 上界与模恒等式体系。
4. J. Salez（2014），计算验证至 10^17（附 C++ 实现；见 erdosproblems.com #242 引用）。
5. D. G. Terzi（1978），覆盖类推进至 mod 120120（转引自 erdosproblems.com #242）。
6. L. J. Mordell, *Diophantine Equations*, Academic Press, 1969——mod 840 六剩余类归约（转引自 Elsholtz 的 Nieuw Archief voor Wiskunde 综述, 2022）。
7. M. Mihnea, C. Dumitru（2025 预印本），计算验证至 10^18（转引自 erdosproblems.com #242 / cairn-commons）。

（注：以上文献均按来源交叉核对；标注「转引自」者为二手来源，未直接核对原文页码。）
