import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Basic
import CmuItp24.Autograde

def F (m : ℕ) : ℕ := 2^(2^m) + 1

theorem succ_le_of_lt {m n : ℕ} (h1 : n < m) : n + 1 ≤ m := by
  exact Nat.succ_le_of_lt h1

theorem power_identity (m n : ℕ) (h : n < m):
  2^(2^m) + 1 = 2^(2^(m - n - 1) * 2^(n + 1)) + 1 := by
  -- Start by simplifying the right-hand side expression
  rw [Nat.pow_mul]
  rw [Nat.pow_add]


  have h : m - n - 1 + (n + 1) = m := by
    rw [Nat.sub_sub]
    have h2 : n + 1 ≤ m := Nat.succ_le_of_lt h

    rw [Nat.sub_add_cancel h2]

  -- rw [Nat.pow_mul]
  rw [←Nat.pow_mul]
  rw [←Nat.pow_add , ←Nat.pow_add]
  rw [h]

theorem power_divisibility (n m : ℕ) (h : n < m) : 2^(2^(n + 1)) - 1 ∣ 2^(2^m) - 1 := by
  -- 使用因式分解性质
  -- 首先表示出 a^n - b^n 的形式，其中 a = 2，b = 1
  let a := 2

  -- 我们需要证明 2^(2^(n+1)) - 1 整除 2^(2^m) - 1
  -- 可以将这些表达式看作是 a^(2^(n+1)) - 1 和 a^(2^m) - 1，其中 a = 2

  -- 由于 n < m，2^(n+1) 是 2^m 的因数，因此可以应用关于 a^k - 1 的因式分解和整除性

  -- 证明思路：考虑因式分解的基本性质 a^(b * k) - 1 = (a^b - 1) * (和项)
  -- 首先，我们把 2^(2^m) - 1 写成 2^(2^(n+1) * k) - 1 的形式
  let b := 2^(n + 1)
  let k := 2^(m - (n + 1))
  have h1 : 2^(2^m) - 1 = (2^(2^(n + 1)))^(2^(m - (n + 1))) - 1 := by
    rw [←Nat.pow_mul]
    congr 1
    rw [Nat.pow_add, Nat.pow_one]

    linarith

  -- 我们可以重写 2^(2^m) - 1 = (a^b)^k - 1
  have h1 : 2^(2^m) - 1 = (a^b)^k - 1 := by
    rw [←Nat.pow_mul]
    congr 1

      _ = 2^(2^(n + 1) * 2^(m - (n + 1))) - 1 : rfl
      _ = 2^(2^m) - 1 : by
        rw [Nat.pow_add, Nat.mul_comm]
        norm_num

  -- 使用指数差的整除性性质：如果 n < m，则 a^(2^m) - 1 可以被 a^(2^(n+1)) - 1 整除
  have h2 : (a^b - 1) ∣ ((a^b)^k - 1) := by
    -- 这里应用指数的整除性定理
    apply Nat.pow_sub_pow
    -- 确保 k > 0
    have h3 : 0 < k := by
      apply Nat.pow_pos
      linarith
    exact h3

  -- 最终结论
  exact h2

theorem power_difference_factorization (n : ℕ) :
  2^(2^(n + 1)) - 1 = (2^(2^n) + 1) * (2^(2^n) - 1) := by
  -- 我们要证明 2^(2^(n + 1)) - 1 的因式分解形式
  -- 使用 (a^n - b^n) 的因式分解公式，其中 a = 2, b = 1
  rw [Nat.pow_add]
  rw [Nat.pow_one, mul_comm]
  rw [Nat.pow_mul]
  have factorization : (2^2)^(2^n) - 1 = (2^(2^n) + 1) * (2^(2^n) - 1) := by
    -- 利用 (a^n - b^n) = (a - b)(a^(n-1) + a^(n-2)b + ... + b^(n-1)) 的性质
    rw [←Nat.pow_mul]
    let a := 2^(2^n)
    have h1 : a ≤ a * a := by
    -- a = 2^(2^n) 是自然数且 a ≥ 1，因此 a * a ≥ a
      apply Nat.le_mul_self
    have h2 : 1 * 1 ≤ 1 * a := by
      -- 由于 a = 2^(2^n) 且 n 是自然数，因此 a ≥ 1
      -- 1 * 1 = 1，而 1 * a = a，因此 1 ≤ a，显然成立
      rw [Nat.one_mul, Nat.one_mul]
      apply Nat.one_le_pow
      norm_num
    have h : a^2 - 1 = (a + 1) * (a - 1) := by
      -- 使用平方差公式：a^2 - b^2 = (a - b) * (a + b)
      rw [Nat.add_mul]
      rw [Nat.mul_sub, Nat.mul_sub]
      rw [←Nat.add_sub_assoc]
      norm_num
      rw [Nat.pow_two]
      rw [Nat.sub_add_cancel]
      exact h1
      exact h2

    rw [Nat.mul_comm]
    rw [Nat.pow_mul]
    rw [←h]
  apply factorization




-- theorem Fermat_mod_property (m n : ℕ) (h : n < m) : 2^(2^m) % F n = 2 := by
--   -- 使用数学归纳法证明此性质
--   induction' m with m ih
--   case zero =>
--     -- 基础情况，这里无法成立，因为 m = 0 不符合 n < m
--     exfalso
--     exact Nat.not_lt_zero n h
--   case succ =>
--     cases n
--     case zero =>
--       -- 当 n = 0 时，F 0 = 3，我们需要证明 2^(2^(m + 1)) ≡ 2 (mod 3)
--       -- 由于 2^2 ≡ 1 (mod 3)，我们可以证明 2^(2^(m + 1)) ≡ 2 (mod 3)
--       have two_squared_mod : 2^2 % 3 = 1 := by norm_num
--       -- 通过归纳得出 2^(2^(m + 1)) ≡ 2 (mod 3)
--       have F0_def : F 0 = 3 := by
--         rw [F]
--         norm_num

--       -- 使用 F 0 = 3 进行替换
--       rw [F0_def]

--       -- 我们要证明 2^(2^(m + 1)) ≡ 2 (mod 3)
--       -- 利用 2 的幂次在模 3 下的循环周期
--       have two_squared_mod : 2^2 % 3 = 1 := by norm_num

--       -- 因为 2^(2^(m + 1)) 的指数 2^(m + 1) 是偶数，利用周期性可得
--       have exp_is_even : ∃ k, 2^(m + 1) = 2 * k := ⟨2^(m), by rw [Nat.pow_succ, mul_comm]⟩

--       rw [Nat.pow_add]
--     --   -- 利用 (2^2)^k % 3 = 1^k = 1
--       rw [Nat.pow_mul]
--       rw [Nat.pow_one]
--       cases Nat.even_or_odd (2^m) with h_even h_odd
--       case inl h_even =>
--         -- 如果 2^m 是偶数，那么 (2^(2^m))^2 % 3 = 1
--         rw [Nat.pow_mul]
--         rw [two_squared_mod]
--         norm_num
--       case inr h_odd =>
--         -- 如果 2^m 是奇数，那么 (2^(2^m))^2 % 3 = 2
--         norm_num
--           rw [two_squared_mod]
--           norm_num
--     case succ n =>
--     --   -- 归纳假设：对于 n < m，2^(2^m) ≡ 2 (mod F n)
--       specialize ih

-- theorem power_mod_Fermat (m n : ℕ) (h : n < m) : 2^(2^m) % (2^(2^n) + 1) = 2 := by
--   -- Step 1: 引入 Fermat 数的定义
--   -- have F_n_def : F n = 2^(2^n) + 1 := rfl

--   -- Step 2: 替换 F n 并进行等价转换
--   -- rw [F_n_def]

--   -- Step 3: 使用 Fermat 数的性质，当 m > n 时，2^(2^m) ≡ 2 (mod F n)
--   -- 在此使用数学归纳法或引用性质证明
--   apply Fermat_mod_property m n h

theorem gcd_Fermat (m n : ℕ) (h : n < m) : Nat.gcd (F m) (F n) = 1 := by
  -- Step 1: 引入 gcd 的定义
  have F_m_def : F m = 2^(2^m) + 1 := rfl
  have F_n_def : F n = 2^(2^n) + 1 := rfl

  -- F m ≡ 2 (mod F n)
  have mod_relation : F m % F n = 2 := by
    rw [F_m_def, F_n_def]
    -- 利用模的性质和幂次运算
    -- 通过 Fermat 数的模运算公式，直接得到此结论
    sorry -- 这里需要进一步的模运算细节

  -- Step 3: 利用 gcd 的性质，我们得到 gcd(F m, F n) = gcd(2, F n)
  have gcd_step : Nat.gcd (F m) (F n) = Nat.gcd 2 (F n) := by
    rw [←mod_relation]
    exact Nat.gcd_rec (F m) (F n) 2

  -- Step 4: F n 是奇数，因此 gcd(2, F n) = 1
  have F_n_odd : F n % 2 = 1 := by
    rw [F_n_def]
    -- 证明 2^(2^n) 是偶数，故加 1 后为奇数
    have even_pow : 2^(2^n) % 2 = 0 := Nat.pow_mod 2 (2^n) 2
    rw [even_pow]
    norm_num

  -- 由此得到 gcd(2, F n) = 1
  have final_gcd : Nat.gcd 2 (F n) = 1 := by
    rw [Nat.gcd_comm]
    apply Nat.gcd_one_right
    exact F_n_odd

  -- 最终结论
  rw [gcd_step, final_gcd]
  rfl
