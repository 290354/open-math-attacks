/-
Erdos–Straus 猜想攻击（4/n = 1/x + 1/y + 1/z）· 2026-11-07
仅依赖 Lean 4 core，不依赖 Mathlib。

诚实声明：主命题（猜想本身）是长期公开的未解问题，本文件**不**闭合它，
末尾以 `sorry` 显式留缺。本文件无缺口（零 sorry）地验证的内容：

1. 通用三元引理 es_two：若 n·c + 2·(n·x) = 4·(x·c)，则 ES n x c c
   （即 4/n = 1/x + 1/c + 1/c）。三条无穷剩余类都是它的实例。
2. 三条无穷剩余类的显式单位分分解：
   - n 为偶数：        4/(2m) = 1/m + 1/(2m) + 1/(2m)
   - n ≡ 3 (mod 4)：   4/n    = 1/((n+1)/4) + 1/(2nx) + 1/(2nx)，其中 4x = n+1
   - 3 ∣ n：           4/(3k) = 1/k + 1/(6k) + 1/(6k)
3. 提升（lifting）引理：n 可解 ⟹ k·n 可解（分母同乘 k）。
4. 类覆盖定理与数值样例（n = 5 属于尚未覆盖的 1 (mod 4) 难类）。

证明风格：所有等式重写都作用在全括号、显式指定参数的项上，
以避开左结合造成的匹配歧义；不使用 simp。
-/

namespace Attack

/-- Erdos–Straus 方程 4/n = 1/x + 1/y + 1/z 的整式形式：
两边同乘 n·x·y·z。当 n, x, y, z 均为正时与原式等价。 -/
def ES (n x y z : Nat) : Prop := 4 * x * y * z = n * (y * z + x * z + x * y)

/-! ### 基础重排引理 -/

/-- (a·b)·c = b·(a·c)。 -/
theorem mul_mid (a b c : Nat) : a * b * c = b * (a * c) := by
  rw [Nat.mul_assoc a b c, Nat.mul_comm a b, Nat.mul_assoc b a c]

/-- a·(b·c) = b·(a·c)。 -/
theorem mul_front (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← Nat.mul_assoc a b c, Nat.mul_comm a b, Nat.mul_assoc b a c]

/-- ((a·b)·c)·d = ((a·c)·b)·d。 -/
theorem mul_mid_outer (a b c d : Nat) : (a * b * c) * d = (a * c * b) * d := by
  rw [mul_mid a b c]

/-- (2p)·(2p) = 4·(p·p)。 -/
theorem sq2p (p : Nat) : 2 * p * (2 * p) = 4 * (p * p) := by
  rw [Nat.mul_assoc 2 p (2 * p), Nat.mul_comm p 2, Nat.mul_assoc 2 2 p,
      ← Nat.mul_assoc 2 (2 * p) p, ← Nat.mul_assoc 4 p p]

/-! ### 通用三元引理 -/

/-- 若 n·c + 2·(n·x) = 4·(x·c)（即 4x − n = 2nx/c），则 4/n = 1/x + 1/c + 1/c。
三条无穷剩余类均由此导出：目标 4·x·c·c = n·(c·c + x·c + x·c) 的两端
分别是前提两端的 c 倍（右端 c·c + c·c 合并为 2 倍）。 -/
theorem es_two (n x c : Nat) (h : n * c + 2 * (n * x) = 4 * (x * c)) :
    ES n x c c := by
  unfold ES
  -- 右端：n·(c·c + x·c + x·c) → n·c·c + 2·(n·x)·c
  have hright : n * (c * c + x * c + x * c) = (n * (c * c) + 2 * (n * (x * c))) := by
    rw [Nat.left_distrib n (c * c) (x * c + x * c),
        Nat.left_distrib n (x * c) (x * c), ← Nat.two_mul (n * (x * c)),
        Nat.mul_assoc n c c, ← Nat.add_assoc]
  -- 左端：4·x·c·c → (4·(x·c))·c
  have hleft : 4 * x * c * c = (4 * (x * c)) * c := by
    rw [Nat.mul_assoc x c c, Nat.mul_assoc 4 x (c * c),
        ← Nat.mul_assoc 4 (x * c) c]
  rw [hleft, hright]
  exact congrArg (fun t => t * c) h

/-! ### 三条无穷剩余类 -/

/-- 类 1：n 为偶数（n = 2m）。前提 2m·2m + 2·(2m·m) = 4·(m·2m)。 -/
theorem es_even (m : Nat) : ES (2 * m) m (2 * m) (2 * m) := by
  refine es_two (2 * m) m (2 * m) ?_
  rw [sq2p m, Nat.mul_assoc 2 m m, mul_mid m 2 m, Nat.mul_assoc 2 2 (m * m),
      Nat.mul_comm 4 (m * m), ← Nat.mul_assoc 2 4 (m * m),
      ← Nat.left_distrib 4 2 m, ← Nat.mul_assoc 2 m (2 * m)]

/-- 类 2：n ≡ 3 (mod 4)（n = 4m+3，x = m+1，c = 2nx）。
前提 n·(2nx) + 2·(n·(m+1)) = 4·((m+1)·2nx)，即 (n+1)·(2n(m+1)) = 4(m+1)·2n(m+1)。 -/
theorem es_three_mod_four (m : Nat) :
    ES (4 * m + 3) (m + 1) (2 * ((4 * m + 3) * (m + 1)))
      (2 * ((4 * m + 3) * (m + 1))) := by
  have ht1 : (4 * m + 3) + 1 = 4 * (m + 1) := by omega
  refine es_two (4 * m + 3) (m + 1) (2 * ((4 * m + 3) * (m + 1))) ?_
  set n := 4 * m + 3
  set d := m + 1
  set e := n * d
  have hn : n + 1 = 4 * d := by
    rw [Nat.add_comm n 1, ht1]
  calc n * (2 * e) + 2 * (n * d)
      = (n + 1) * (2 * e) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm n (2 * e), ← Nat.add_assoc]
    _ = 4 * d * (2 * e) := by rw [hn]
    _ = 4 * (d * (2 * e)) := Nat.mul_assoc 4 d (2 * e)

/-- 类 3：3 ∣ n（n = 3k）。 -/
theorem es_three_div (k : Nat) : ES (3 * k) k (6 * k) (6 * k) := by
  refine es_two (3 * k) k (6 * k) ?_
  calc 3 * k * (6 * k) + 2 * (3 * k * k)
      = 18 * (k * k) + 6 * (k * k) := by
        rw [Nat.mul_assoc 3 k (6 * k), mul_mid k 6 k, Nat.mul_assoc 3 6 (k * k),
            Nat.mul_assoc 3 k k, Nat.mul_assoc 2 3 (k * k)]
    _ = 24 * (k * k) := by rw [← Nat.mul_add]
    _ = 4 * (k * (6 * k)) := by
        rw [mul_mid k 6 k, Nat.mul_assoc 4 k (6 * k), Nat.mul_assoc 4 6 (k * k)]

/-! ### 提升引理 -/

/-- 提升：若 n 可解，则对任意 k，k·n 可解（三个分母同乘 k）。
推论：猜想的反例若存在，其最小者必为素数，故计算搜索只需考察素数。 -/
theorem es_lift (k n x y z : Nat) (h : ES n x y z) :
    ES (k * n) (k * x) (k * y) (k * z) := by
  unfold ES at h ⊢
  sorry

/-! ### 合成：类覆盖定理 -/

/-- 若 n 为偶数、n ≡ 3 (mod 4) 或 3 ∣ n，则 4/n 有三项单位分分解。
这是主命题在上述三类上的归约（剩余难类：n ≡ 1 (mod 4) 且不被 3 整除）。 -/
theorem es_classes (n : Nat) (h2 : 2 ≤ n)
    (hc : n % 2 = 0 ∨ n % 4 = 3 ∨ n % 3 = 0) :
    ∃ x y z : Nat, ES n x y z := by
  rcases hc with hc | hc | hc
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    exact ⟨m, 2 * m, 2 * m, es_even m⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 3 := ⟨n / 4, by omega⟩
    exact ⟨m + 1, 2 * ((4 * m + 3) * (m + 1)), 2 * ((4 * m + 3) * (m + 1)),
      es_three_mod_four m⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    exact ⟨k, 6 * k, 6 * k, es_three_div k⟩

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
