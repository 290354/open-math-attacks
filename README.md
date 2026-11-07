# Open Math Attacks

每天尝试一个**长期公开的未解决数学问题**：选题 → 可行性预判 → 真实攻关 → Lean 4 形式化 → 如实汇报。

## 这个仓库是什么

不是「每天解决一个难题」的成果展。绝大多数数学未解问题需要数年甚至数十年，任何声称「每日一解」的产出几乎必然是错的。

所以仓库的规则是：**允许失败，禁止造假。**

每次记录按正确性分级标注，只有最高级才允许出现「已证明」字样。

## 正确性分级

| 级别 | 含义 | 允许的措辞 |
|---|---|---|
| **L3** | 主定理在 Lean 4 中完整形式化，`lake build` 通过，全文 0 个 `sorry`，未新增 `axiom`，未用 `native_decide` 逃逸 | 「已证明」 |
| **L2** | 关键引理已形式化，主定理仍有缺口 | 「部分形式化」 |
| **L1** | 仅命题陈述已形式化，证明为人工论证 | 「未验证的尝试」 |
| **L0** | 无形式化，仅计算/数值证据 | 「实验性证据」 |

## 目录结构

```
YYYY-MM-DD-<slug>/
├── README.md         # 选题理由、方法、结论、可信度级别、失败原因
├── paper/
│   ├── paper.md      # 论文/报告正文
│   └── paper.tex     # LaTeX 版本
├── lean/             # Lean 4 工程（lakefile.toml + 源文件）
└── scripts/          # 可复现的计算/搜索脚本
```

## 硬性规则

1. 任何「已证明」结论必须过 Lean 闸门（L3），否则只能标注为尝试。
2. 禁止编造文献、定理编号、作者年份。
3. 禁止把「小规模验证」写成「对所有 n 成立」。
4. 所有数值主张必须附可复现脚本。
5. 未取得完整证明时，产出「部分结果 + 失败原因分析 + 下一步路线图」，这同样是有效产出。

## 选题来源

- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Erdős Problems](https://www.erdosproblems.com/)
- [MathOverflow open-problems](https://mathoverflow.net/questions/tagged/open-problems)
- [AIM Problem Lists](https://aimath.org/problem-lists/)
- OEIS 中的猜想条目

## 免责声明

本仓库内容由自动化系统生成，**未经同行评审**。请按上表的可信度分级阅读，不要把 L0–L2 的内容当作已确立的数学结论引用。
