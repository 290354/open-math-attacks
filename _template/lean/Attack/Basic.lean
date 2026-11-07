/-
模板工程：仅依赖 Lean 4 core，不依赖 Mathlib。

为什么不用 Mathlib：本环境的网络下载速度只有约 1 MB/min，
Mathlib 的源码加缓存有数 GB，无法在单次任务的时限内就位。
因此形式化范围限定为「Lean core 能表达的陈述与证明」。

用法：把整个 lean/ 目录复制到本轮目录下，改 lakefile.toml 里的 name，
然后 lake build。CI（.github/workflows/lean-verify.yml）会在 push 后自动
构建仓库里所有 */lean 工程，读取编译器的未完成证明告警，并扫描自定义公理。
-/

namespace Attack

/-- 冒烟测试：确认工具链与构建链路可用。 -/
theorem smoke_two_add_two : 2 + 2 = 4 := rfl

/-- 引用 core 里已有的交换律，确认依赖解析正常。 -/
theorem smoke_add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- 一条需要真正证明步骤的引理，确认 tactic 模式可用。 -/
theorem smoke_pred_lt (n : Nat) (h : 0 < n) : n - 1 < n := by
  omega

end Attack
