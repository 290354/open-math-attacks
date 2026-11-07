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
   由此，猜想的反例若存在，其最小者必为素数。
4. 类覆盖定理与数值样例（n = 5 属于尚未覆盖的 1 (mod 4) 难类）。

证明风格：只使用「乘法结合律 + 乘法左交换 + 乘法对加法的分配律 + 加法交换/结合」
这些有方向的等式重写，避免 simp 在非线性项上的不可预测行为。
-/

namespace Attack

/-- Erdos–Straus 方程 4/n = 1/x + 1/y + 1/z 的整式形式：
两边同乘 n·x·y·z。当 n, x, y, z 均为正时与原式等价。 -/
def ES (n x y z : Nat) : Prop := 4 * x * y * z = n * (y * z + x * z + x * y)

/-! ### 基础重排引理（全部为有方向的等式，可安全 rw） -/

/-- 把最左侧因子搬到第二位置：a·(b·c) = b·(a·c)。 -/
theorem mulL3 (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← Nat.mul_assoc a b c, Nat.mul_comm a b, Nat.mul_assoc b a c]

/-- (2p)·(2p) = 4·(p·p)。 -/
theorem sq2p (p : Nat) : (2 * p) * (2 * p) = 4 * (p * p) := by
  rw [Nat.mul_assoc 2 p (2 * p), mulL3 p 2 p, ← Nat.mul_assoc 2 2 (p * p)]

/-- c·t + c·t = 2·(c·t)。 -/
theorem add_self (c t : Nat) : c * t + c * t = 2 * (c * t) := (Nat.two_mul (c * t)).symm

/-! ### 通用三元引理 -/

/-- 若 n·c + 2·(n·x) = 4·(x·c)（即 4x − n = 2nx/c），则 4/n = 1/x + 1/c + 1/c。
三条无穷剩余类均由此导出。 -/
theorem es_two (n x c : Nat) (h : n * c + 2 * (n * x) = 4 * (x * c)) :
    ES n x c c := by
  unfold ES
  -- 前提两边同乘 c
  have hc : n * (c * c) + 2 * (n * (x * c)) = 4 * (x * (c * c)) := by
    have h5 := congrArg (fun t => t * c) h
    rw [Nat.add_mul,
        Nat.mul_assoc 2 (n * x) c, Nat.mul_assoc n x c,
        Nat.mul_assoc n c c,
        Nat.mul_assoc 4 (x * c) c, Nat.mul_assoc x c c] at h5
    exact h5
  -- 目标右端：4·(x·c)·c = (4·(x·(c·c)))·1 → 提成 c·(…)
  rw [Nat.mul_assoc (4 * x) c c, Nat.mul_assoc 4 x (c * c)]
  rw [← Nat.mul_assoc 4 (x * (c * c)) c, ← Nat.two_mul]
  rw [← Nat.mul_add, ← Nat.mul_assoc 2 (x * (c * c)) c]
  rw [Nat.mul_comm 2 (x * (c * c)), Nat.mul_assoc (x * (c * c)) 2 c,
      ← Nat.mul_assoc 4 (x * (c * c)) c, Nat.mul_assoc 4 x (c * c)]
  -- 目标左端：n·(c·c) + n·(x·c)·c·2
  rw [Nat.mul_assoc (n * x) c c, mulL3 (n * x) c c, ← Nat.mul_assoc (n * c) (x * c) c]
  rw [Nat.mul_assoc n c c, Nat.mul_assoc 2 (n * (x * c)) c,
      ← Nat.mul_add, ← Nat.mul_assoc (n * (c * c) + 2 * (n * (x * c))) c]
  exact congrArg (fun t => t * c) hc.symm

/-! ### 三条无穷剩余类 -/

/-- 类 1：n 为偶数（n = 2m）。 -/
theorem es_even (m : Nat) : ES (2 * m) m (2 * m) (2 * m) := by
  have h : (2 * m) * (2 * m) + 2 * ((2 * m) * m) = 4 * (m * (2 * m)) := by
    rw [sq2p m, Nat.mul_assoc 2 m m, mulL3 m 2 m]
    rw [← Nat.mul_add, ← Nat.mul_assoc 4 2 (m * m), Nat.mul_assoc 4 m (2 * m)]
  exact es_two (2 * m) m (2 * m) h

/-- 类 2：n ≡ 3 (mod 4)（n = 4m+3，x = m+1，c = 2nx）。 -/
theorem es_three_mod_four (m : Nat) :
    ES (4 * m + 3) (m + 1) (2 * ((4 * m + 3) * (m + 1)))
      (2 * ((4 * m + 3) * (m + 1))) := by
  have ht1 : (4 * m + 3) + 1 = 4 * (m + 1) := by omega
  have hQ : (4 * m + 3) * ((4 * m + 3) * (m + 1)) + (4 * m + 3) * (m + 1)
      = 4 * ((m + 1) * ((4 * m + 3) * (m + 1))) := by
    have h2 : ((4 * m + 3) + 1) * ((4 * m + 3) * (m + 1))
        = 4 * ((m + 1) * ((4 * m + 3) * (m + 1))) := by
      rw [ht1, Nat.mul_assoc 4 (m + 1) ((4 * m + 3) * (m + 1))]
    rw [Nat.add_mul (4 * m + 3) 1 ((4 * m + 3) * (m + 1)), Nat.one_mul] at h2
    exact h2
  have h : (4 * m + 3) * (2 * ((4 * m + 3) * (m + 1)))
      + 2 * ((4 * m + 3) * (m + 1))
      = 4 * ((m + 1) * (2 * ((4 * m + 3) * (m + 1)))) := by
    rw [mulL3 (4 * m + 3) 2 ((4 * m + 3) * (m + 1))]
    rw [← Nat.mul_add 2 ((4 * m + 3) * ((4 * m + 3) * (m + 1)))
          ((4 * m + 3) * (m + 1)), hQ]
    rw [mulL3 (m + 1) 2 ((4 * m + 3) * (m + 1)), ← Nat.two_mul,
        ← Nat.mul_assoc 4 2 ((m + 1) * ((4 * m + 3) * (m + 1)))]
  exact es_two (4 * m + 3) (m + 1) (2 * ((4 * m + 3) * (m + 1))) h

/-- 类 3：3 ∣ n（n = 3k）。 -/
theorem es_three_div (k : Nat) : ES (3 * k) k (6 * k) (6 * k) := by
  have e1 : (3 * k) * (6 * k) = 18 * (k * k) := by
    rw [Nat.mul_assoc 3 k (6 * k), mulL3 k 6 k, ← Nat.mul_assoc 3 6 (k * k)]
  have e2 : (3 * k) * k = 3 * (k * k) := Nat.mul_assoc 3 k k
  have e3 : k * (6 * k) = 6 * (k * k) := mulL3 k 6 k
  have h : (3 * k) * (6 * k) + 2 * ((3 * k) * k) = 4 * (k * (6 * k)) := by
    rw [e1, e2, e3]
    rw [Nat.mul_assoc 2 3 (k * k), Nat.mul_assoc 4 6 (k * k), ← Nat.mul_add]
  exact es_two (3 * k) k (6 * k) h

/-! ### 提升引理 -/

/-- 单因子：k·(k·(k·x)) = (k·k)·(k·x)。 -/
theorem kkk (k x : Nat) : k * (k * (k * x)) = k * k * (k * x) :=
  (Nat.mul_assoc k k (k * x)).symm

/-- 合并前两个因子：(k·x)·(k·y) = k·(k·(x·y))。 -/
theorem mul_pair (k x y : Nat) : (k * x) * (k * y) = k * (k * (x * y)) := by
  rw [Nat.mul_assoc (k * x) k y, mulL3 (k * x) k y, Nat.mul_assoc k x y,
      Nat.mul_assoc k k (x * y)]

/-- 内外两层各乘一个因子：(a·b)·(c·d) = (a·c)·(b·d)。 -/
theorem mul_swap4 (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc a b (c * d), Nat.mul_assoc a c (b * d), Nat.mul_assoc b c d,
      ← Nat.mul_assoc c b d, Nat.mul_comm c b]

/-- 乘法三重重排：(k·x)·(k·y)·(k·z) = k·(k·(k·(x·y·z)))。 -/
theorem mul_k3 (k x y z : Nat) :
    (k * x) * (k * y) * (k * z) = k * (k * (k * (x * y * z))) := by
  rw [mul_pair k x y, mul_pair k (k * (x * y)) z,
      Nat.mul_assoc k (x * y) z]

/-- 分配律展开：(k·y)·(k·z) + (k·x)·(k·z) + (k·x)·(k·y)
= k·(k·(k·(y·z + x·z + x·y)))。 -/
theorem dist_k3 (k x y z : Nat) :
    (k * y) * (k * z) + (k * x) * (k * z) + (k * x) * (k * y)
      = k * (k * (k * (y * z + x * z + x * y))) := by
  have h1 : (k * y) * (k * z) = k * (k * (y * z)) := by
    rw [Nat.mul_assoc (k * y) k z, mulL3 (k * y) k z, Nat.mul_assoc k y z,
        Nat.mul_assoc k k (y * z)]
  have h2 : (k * x) * (k * z) = k * (k * (x * z)) := by
    rw [Nat.mul_assoc (k * x) k z, mulL3 (k * x) k z, Nat.mul_assoc k x z,
        Nat.mul_assoc k k (x * z)]
  have h3 : (k * x) * (k * y) = k * (k * (x * y)) := by
    rw [Nat.mul_assoc (k * x) k y, mulL3 (k * x) k y, Nat.mul_assoc k x y,
        Nat.mul_assoc k k (x * y)]
  rw [h1, h2, h3, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]

/-- 提升：若 n 可解，则对任意 k，k·n 可解（三个分母同乘 k）。
推论：猜想的反例若存在，其最小者必为素数，故计算搜索只需考察素数。 -/
theorem es_lift (k n x y z : Nat) (h : ES n x y z) :
    ES (k * n) (k * x) (k * y) (k * z) := by
  unfold ES at h ⊢
  rw [mul_k3, dist_k3, ← Nat.mul_assoc (k * n) k _, ← Nat.mul_assoc (k * n) k _]
  rw [Nat.mul_assoc k n _, ← Nat.mul_assoc k k _, h]

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
