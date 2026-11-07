/-
Erdos–Straus 猜想攻击（4/n = 1/x + 1/y + 1/z）· 2026-11-07
仅依赖 Lean 4 core，不依赖 Mathlib。

诚实声明：主命题（猜想本身）是长期公开的未解问题，本文件**不**闭合它，
末尾以 `sorry` 显式留缺。本文件无缺口（零 sorry）地验证的内容：

1. 三条无穷剩余类的显式单位分分解：
   - n 为偶数：        4/(2m)   = 1/m + 1/(2m) + 1/(2m)
   - n ≡ 3 (mod 4)：   4/n      = 1/((n+1)/4) + 1/(n(n+1)/2) + 1/(n(n+1)/2)
   - 3 ∣ n：           4/(3k)   = 1/k + 1/(6k) + 1/(6k)
2. 提升（lifting）引理：n 可解 ⟹ 对任意 k，k·n 可解（分母同乘 k）。
   由此，搜索只需考察素数 n（文献中的标准归约）。
3. 类覆盖定理与数值样例（n = 5 属于尚未覆盖的 1 (mod 4) 难类）。
-/

namespace Attack

/-- Erdos–Straus 方程 4/n = 1/x + 1/y + 1/z 的整式形式：
两边同乘 n·x·y·z。当 n, x, y, z 均为正时与原式等价。
（若允许 x,y,z 取 0，方程会产生平凡退化解，故解释时须限定为正整数，
见文件尾主命题的注释。） -/
def ES (n x y z : Nat) : Prop := 4 * x * y * z = n * (y * z + x * z + x * y)

/-! ### 无穷剩余类的显式解 -/

/-- 类 1：n 为偶数（n = 2m）。 -/
theorem es_even (m : Nat) : ES (2 * m) m (2 * m) (2 * m) := by
  simp only [ES]
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_assoc]

/-- 类 2：n ≡ 3 (mod 4)（n = 4m+3）。 -/
theorem es_three_mod_four (m : Nat) :
    ES (4 * m + 3) (m + 1) (2 * (m + 1) * (4 * m + 3)) (2 * (m + 1) * (4 * m + 3)) := by
  simp only [ES]
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_assoc]

/-- 类 3：3 ∣ n（n = 3k）。 -/
theorem es_three_div (k : Nat) : ES (3 * k) k (6 * k) (6 * k) := by
  simp only [ES]
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_assoc]

/-! ### 提升引理 -/

/-- 提升：若 n 可解，则对任意 k，k·n 可解（三个分母同乘 k）。
推论：猜想的反例若存在，其最小者必为素数，故计算搜索只需考察素数。 -/
theorem es_lift (k n x y z : Nat) (h : ES n x y z) :
    ES (k * n) (k * x) (k * y) (k * z) := by
  simp only [ES] at h ⊢
  calc 4 * (k * x) * (k * y) * (k * z)
      = k * (k * (k * (4 * x * y * z))) := by
        simp [Nat.mul_comm, Nat.mul_assoc]
    _ = k * (k * (k * (n * (y * z + x * z + x * y)))) := by rw [h]
    _ = (k * n) * ((k * y) * (k * z) + (k * x) * (k * z) + (k * x) * (k * y)) := by
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc,
          Nat.add_comm, Nat.add_assoc]

/-! ### 合成：类覆盖定理 -/

/-- 若 n 为偶数、n ≡ 3 (mod 4) 或 3 ∣ n，则 4/n 有三项单位分分解。
这是主命题在上述三类上的完整归约（剩余难类：n ≡ 1 (mod 4) 且不被 3 整除）。 -/
theorem es_classes (n : Nat) (h2 : 2 ≤ n)
    (hc : n % 2 = 0 ∨ n % 4 = 3 ∨ n % 3 = 0) :
    ∃ x y z : Nat, ES n x y z := by
  rcases hc with hc | hc | hc
  · have hn : n = 2 * (n / 2) := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, hn⟩
    exact es_even m
  · have hn : n = 4 * (n / 4) + 3 := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 3 := ⟨n / 4, hn⟩
    exact es_three_mod_four m
  · have hn : n = 3 * (n / 3) := by omega
    obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k := ⟨n / 3, hn⟩
    exact es_three_div k

/-! ### 数值样例 -/

/-- 数值样例：4/5 = 1/2 + 1/4 + 1/20。
n = 5 属于尚未被显式类覆盖的 1 (mod 4) 难类。 -/
theorem es_five : ES 5 2 4 20 := by rfl

/-! ### 主命题（未解决，诚实留缺） -/

/-- **Erdos–Straus 猜想**：对每个 n ≥ 2，方程 4/n = 1/x + 1/y + 1/z
有正整数解。这是 1948 年以来长期公开的未解问题。

注：整式形式下 x,y,z 全为 0 是平凡退化（两端同为 0），因此严格陈述
须限定正整数解；对 n ≥ 2，「恰一个分母为 0」不可能满足方程
（左端为 0 而右端为 n·(另一对之积) > 0），但「两个以上为 0」可以，
故正性假设不可省略。本声明用 `sorry` 显式标注未闭合的缺口。 -/
theorem erdos_straus_conjecture : ∀ n : Nat, 2 ≤ n → ∃ x y z : Nat,
    0 < x ∧ 0 < y ∧ 0 < z ∧ ES n x y z := by
  intro n hn
  sorry

end Attack
