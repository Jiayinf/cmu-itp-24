import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import CmuItp24.Autograde


-- Before the project : This ia a proof op Fermat numbers are coprime.
-- The final Fermat prove result is at the very end of the file Line 375.
-- Before, it inculdes a lot of necessary step proofs.

def F (m : ℕ) : ℕ := 2^(2^m) + 1

variable {m n : ℕ}

theorem succ_le_of_lt {m n : ℕ} (h1 : n < m) : n + 1 ≤ m := by
  exact Nat.succ_le_of_lt h1


theorem n_less_m {m n : ℕ} (h : n < m): n + 1 ≤ m := Nat.succ_le_of_lt h

lemma power_identity (m n : ℕ) (h : n < m):
  2^(2^m) = 2^(2^(m - n - 1) * 2^(n + 1)) := by
  -- Start by simplifying the right-hand side expression
  rw [Nat.pow_mul]
  rw [Nat.pow_add]

  have h2 : n + 1 ≤ m := Nat.succ_le_of_lt h

  have h : m - n - 1 + (n + 1) = m := by
    rw [Nat.sub_sub]


    rw [Nat.sub_add_cancel h2]

  -- rw [Nat.pow_mul]
  rw [←Nat.pow_mul]
  rw [←Nat.pow_add , ←Nat.pow_add]
  rw [h]

theorem power_divisible (a b x : ℕ) (h : b ≤ a) : (a - b) ∣ (a ^ x - b ^ x) := by
  -- 对 x 进行数学归纳
  induction' x with k ih
  case zero =>
    -- 基础情况 x = 0
    -- a^0 - b^0 = 1 - 1 = 0，总是被 (a - b) 整除
    exact nat_sub_dvd_pow_sub_pow a b 0

  have h1 : a^(k + 1) - b^(k + 1) = a * a^k - b * b^k := by
    rw [Nat.pow_succ, Nat.pow_succ]
    rw [mul_comm, mul_comm b]
  have h2 : a * a^k - b * b^k = (a - b) * a^k + b * (a^k - b^k) := by
    rw [Nat.sub_mul, Nat.mul_sub, ←Nat.add_sub_assoc]
    rw [Nat.sub_add_cancel]
    apply Nat.mul_le_mul_right
    exact h
    apply Nat.mul_le_mul_left
  -- 使用假设 b ≤ a 和幂次的单调性来证明 b^k ≤ a^k
    apply Nat.pow_le_pow_of_le_left h

  rw [h1]
  rw [h2]
  apply dvd_add
  exact Nat.dvd_mul_right (a - b) (a ^ k)
  exact Dvd.dvd.mul_left ih b


theorem power_divisibility (n m : ℕ) (h : n < m) : 2^(2^(n + 1)) - 1 ∣ 2^(2^m) - 1 := by

  -- let a := 2^(2^(n + 1))
  -- let b := 1
  -- let x := 2^(m - (n + 1))

  induction' 2^(m - (n + 1)) with k ih
  case zero =>
    -- have h3 : m - n - 1 + (n + 1) = m := by
    --   rw [Nat.sub_sub]
    --   rw [Nat.sub_add_cancel]
    --   apply n_less_m
    --   apply h
    -- have power_divisibility_simplify (n m : ℕ) (h : n < m) :
    --   2 ^ 2 ^ (n + 1) - 1 ∣ 2 ^ 2 ^ (m - (n + 1) + (n + 1)) - 1 := by

    -- have h1 : m - (n + 1) + (n + 1) = m := by
    --   rw [Nat.sub_add_cancel]
    --   apply n_less_m
    --   apply h

    -- 使用 h1 重写表达式，将 `(m - (n + 1) + (n + 1))` 替换为 `m

    -- 接下来，将 `2 ^ (2 ^ m)` 表示为 `2 ^ (2 ^ (m - (n + 1)) * 2 ^ (n + 1))`
    have h2 : 2 ^ 2 ^ m = 2 ^ (2 ^ (m - (n + 1)) * 2 ^ (n + 1)) := by
      rw [←Nat.sub_sub, ←Nat.pow_add, Nat.sub_sub, Nat.sub_add_cancel]
      apply n_less_m
      apply h
    -- 使用 h2 重写表达式
    rw [h2]
    rw [mul_comm]
    rw [Nat.pow_mul]
    have h_one: (2 ^ 2 ^ (n + 1)) ^ 2 ^ (m - (n + 1)) - 1 = (2 ^ 2 ^ (n + 1)) ^ 2 ^ (m - (n + 1)) - 1 ^ (2^(m - (n + 1))) := by
      rw [Nat.one_pow]
    rw [h_one]

    exact nat_sub_dvd_pow_sub_pow (2 ^ 2 ^ (n + 1)) 1 (2 ^ (m - (n + 1)))


  case succ =>
    have hk : 1 ≤ 2^(2^(n + 1)) := by
      apply Nat.one_le_pow
      norm_num
    let a := 2^(2^(n + 1))
    let b := 1
    have h11 : a^(k + 1) - b^(k + 1) = a * a^k - b * b^k := by
        rw [Nat.pow_succ, Nat.pow_succ]
        simp [mul_comm]

    have h1 : (2^(2^(n + 1)))^(k + 1) - 1^(k + 1) = (2^(2^(n + 1))) * (2^(2^(n + 1)))^k - 1 * 1^k := by
      rw [Nat.pow_succ, Nat.pow_succ]
      rw [mul_comm, mul_comm 1]
      simp

    have h2 : (2^(2^(n + 1))) * (2^(2^(n + 1)))^k - 1 * 1^k = ((2^(2^(n + 1))) - 1) * (2^(2^(n + 1)))^k + 1 * ((2^(2^(n + 1)))^k - 1^k) := by
      rw [Nat.sub_mul, Nat.mul_sub, ←Nat.add_sub_assoc]
      rw [Nat.sub_add_cancel]
      apply Nat.mul_le_mul_right
      exact hk
      apply Nat.mul_le_mul_left
    -- 使用假设 b ≤ a 和幂次的单调性来证明 b^k ≤ a^k
      apply Nat.pow_le_pow_of_le_left hk


    have h2 : 2 ^ 2 ^ m = 2 ^ (2 ^ (m - (n + 1)) * 2 ^ (n + 1)) := by
      rw [←Nat.sub_sub, ←Nat.pow_add, Nat.sub_sub, Nat.sub_add_cancel]
      apply n_less_m
      apply h
      -- 使用 h2 重写表达式
    rw [h2]
    rw [mul_comm]
    rw [Nat.pow_mul]
    have h_one: (2 ^ 2 ^ (n + 1)) ^ 2 ^ (m - (n + 1)) - 1 = (2 ^ 2 ^ (n + 1)) ^ 2 ^ (m - (n + 1)) - 1 ^ (2^(m - (n + 1))) := by
      rw [Nat.one_pow]
    rw [h_one]
    exact power_divisible (2 ^ 2 ^ (n + 1)) 1 (2 ^ (m - (n + 1))) hk
    -- rw [h1]
    -- rw [h2]
    -- apply dvd_add
    -- exact Nat.dvd_mul_right ((2^(2^(n + 1))) - 1) ((2^(2^(n + 1))) ^ k)
    -- exact Dvd.dvd.mul_left ih b




  -- have h1 : 2^(2^n * 2 * 2^(m - (n + 1))) = 2^((2^n * 2) * 2^(m - (n + 1))) := by
  --   rw [Nat.mul_assoc]
  -- have h2 : 2^n * 2 * 2^(m - (n + 1)) = 2^m := by
  --   -- 将 2^n * 2 重写为 2^(n + 1)
  --   rw [mul_assoc]
  --   rw [←Nat.sub_sub]
  --   rw [←mul_assoc]
  --   rw [mul_comm, ←mul_assoc]
  --   rw [←Nat.pow_add]
  --   rw [mul_comm]
  --   have h3 : m - n - 1 + n + 1 = m := by
  --     rw [add_assoc]
  --     rw [Nat.sub_sub]
  --     rw [Nat.sub_add_cancel h4]

  --   rw [←Nat.pow_one 2]
  --   rw [←Nat.pow_add]
  --   rw [add_comm]
  --   rw [Nat.pow_one]
  --   rw [h3]

  -- have h5 : 2^(2^m) - 1 = (2^2^(n + 1))^2^(m - (n + 1)) - 1 := by
  --   have b_mul_k : 2^(n + 1) * 2^(m - (n + 1)) = 2^m := by
  --     rw [Nat.pow_add]
  --     rw [Nat.pow_one]
  --     rw [h2]

  --   rw [←Nat.pow_mul]
  --   rw [b_mul_k]

  -- use 2 ^ (m - (n + 1))



  -- have divisibility (a b : ℕ) : a - b ∣ a^2 - b^2 := by
  --   have h (a b : ℕ) (h : b < a): a^2 - b^2 = (a - b) * (a + b) := by
  --     rw [Nat.pow_two, Nat.pow_two, mul_comm (a - b)]
  --     rw [Nat.mul_sub_left_distrib]
  --   exact nat_sub_dvd_pow_sub_pow a b 2

-- lemma ab (n m : ℕ): n % m = 0 := by
--   sorry
-- lemma kkl (m : ℕ) (h : 2 < m) : 2 % m = 2 := by
--   -- 使用 `Nat.mod_eq_of_lt` 来证明，当 `2 < m` 时 `2 % m = 2`
--   exact Nat.mod_eq_of_lt h
-- example (n m : ℕ) (hll : 2 < m): (n + 2) % m = 2 := by
--   have h := ab n m
--   rw [Nat.add_mod, h]
--   simp
--   apply kkl
--   apply hll
theorem power_greater_than_two (n : ℕ) : 2 ^ (2 ^ (n + 1)) - 1 > 2 := by
  have hk : n ≥ 0 := Nat.zero_le n
  have h1 : n + 1 ≥ 1 := Nat.succ_le_succ hk
  -- 因此 `2 ^ (n + 1) ≥ 2 ^ 2 = 4`
  have h2 : 2 ^ (n + 1) ≥ 2 := Nat.pow_le_pow_of_le_right (Nat.succ_pos 1) h1
  -- 从而 `2 ^ (2 ^ (n + 1)) ≥ 2 ^ 4 = 16`
  have h3 : 4 ≤ 2 ^ (2 ^ (n + 1)) := Nat.pow_le_pow_of_le_right (Nat.succ_pos 1) h2
  -- 最后，`2 ^ (2 ^ (n + 1)) - 1 ≥ 16 - 1 = 15 > 2`
  have h4 : 2 ^ (2 ^ (n + 1)) - 1 ≥ 3 := by
    apply Nat.sub_le_sub_right h3 1
  -- 最终得出 15 > 2
  linarith

theorem power_mod_zero (n m : ℕ) (h : n < m) : (2 ^ (2 ^ m) - 1) % (2 ^ (2 ^ (n + 1)) - 1) = 0 := by
  have div_result := power_divisibility n m h
  exact Nat.dvd_iff_mod_eq_zero.mp div_result



theorem power_mod_two (n m : ℕ) (h : n < m): (2 ^ (2 ^ m) - 1 + 2) % (2 ^ (2 ^ (n + 1)) - 1) = 2 := by
  have hn : n ≥ 0 := Nat.zero_le n
  have mod_zero := power_mod_zero n m h
  rw [Nat.add_mod, mod_zero]
  simp
  have h2 : 2 < 2 ^ (2 ^ (n + 1)) - 1 := by
    -- 使用 `power_greater_than_two` 证明 2 ^ (2 ^ (n + 1)) - 1 > 2
    exact power_greater_than_two n
  -- 因为 2 < 2 ^ (2 ^ (n + 1)) - 1，所以 2 % (2 ^ (2 ^ (n + 1)) - 1) = 2
  exact Nat.mod_eq_of_lt h2




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

-- example (a b c : ℕ) (h1: a % (b * c) = 2): ∃ d : ℕ, a = (b * c)*d + 2 := by
--   apply?


example (a b c : ℕ) (h1: a % (b * c) = 2) (h2: b > 2): a % b = 2 := by
  have h3 : a % (b * c) % b = 2 := by
    exact Nat.mod_eq_of_modEq (congrFun (congrArg HMod.hMod h1) b) h2
  rw [←h3]
  rw [Nat.mod_mul_right_mod a b c]


theorem power_difference_divisible (n : ℕ) :
  (2^(2^n) + 1) ∣ (2^(2^(n + 1)) - 1) := by
  -- 使用已知的因式分解 `power_difference_factorization`
  have h := power_difference_factorization n
  -- 根据因式分解，得出 `(2^(2^n) + 1) | (2^(2^(n + 1)) - 1)`
  rw [h]
  -- 使用 `dvd_mul_right`，因为 `(2^(2^n) + 1)` 是右边乘积的因子
  exact dvd_mul_right (2 ^ (2 ^ n) + 1) (2 ^ (2 ^ n) - 1)

lemma power_mod_two_new (m n : ℕ) (h : n < m) :
  (2 ^ 2 ^ m + 1) % (2 ^ 2 ^ n + 1) = 2 := by
  have mod_two := power_mod_two n m h
  have factorization := power_difference_factorization n
  -- 将表达式重写为所需的模运算形式

  have h2 : 2 < 2 ^ (2 ^ n) + 1 := by
    have hk : n ≥ 0 := Nat.zero_le n
    have ha : 2 ^ n ≥ 1 := by
      exact Nat.one_le_two_pow

    have hb : 2 ^ (2 ^ n) ≥ 2 ^ 1 := by
      exact Nat.pow_le_pow_of_le_right (Nat.succ_pos 1) ha

    have hl: 2 + 1 ≤ 2 ^ (2 ^ n) + 1:= by
      exact Nat.add_le_add_right hb 1

    have hll: 3 ≤ 2 ^ (2 ^ n) + 1:= by
      exact hl

    have less3 : 2 < 3 := by norm_num
    exact hl

  have h6 : (2 ^ 2 ^ m - 1 + 2) % ((2 ^ 2 ^ n + 1) * (2 ^ 2 ^ n - 1)) = 2 := by
    rw [factorization] at mod_two
    exact mod_two
  have h9 : (2 ^ 2 ^ m + 1) % ((2 ^ 2 ^ n + 1) * (2 ^ 2 ^ n - 1)) = 2 := by
    rw [factorization] at mod_two
    have hll : (2 ^ 2 ^ m + 1) = (2 ^ 2 ^ m - 1 + 2) := by
      norm_num
      rw[Nat.sub_add_cancel]
      exact Nat.one_le_two_pow
    rw [hll]
    exact h6

  have h7 : (2 ^ 2 ^ m + 1) % ((2 ^ 2 ^ n + 1) * (2 ^ 2 ^ n - 1)) % (2 ^ 2 ^ n + 1) = 2 := by
    exact Nat.mod_eq_of_modEq (congrFun (congrArg HMod.hMod h9) (2 ^ 2 ^ n + 1)) h2

  -- have h8 : (2 ^ 2 ^ m + 1) % ((2 ^ 2 ^ n + 1) * (2 ^ 2 ^ n - 1)) = (2 ^ 2 ^ m + 1) % ((2 ^ 2 ^ n + 1) * (2 ^ 2 ^ n - 1)) % (2 ^ 2 ^ n + 1) := by
  --   rw[h7,h9]

  have h10 : (2 ^ 2 ^ m + 1) % (2 ^ 2 ^ n + 1) = (2 ^ 2 ^ m + 1) % ((2 ^ 2 ^ n + 1) * (2 ^ 2 ^ n - 1)) % (2 ^ 2 ^ n + 1) := by
    exact Eq.symm (Nat.mod_mul_right_mod (2 ^ 2 ^ m + 1) (2 ^ 2 ^ n + 1) (2 ^ 2 ^ n - 1))

  rw [h10]
  rw [h7]


theorem gcd_power_two (m n : ℕ) (h : n < m):
  Nat.gcd (2 ^ (2 ^ n) + 1) (2 ^ (2 ^ m) + 1) = Nat.gcd 2 (2 ^ (2 ^ n) + 1) := by
  -- 利用 gcd 的性质，我们可以将 gcd(a, b) 写成 gcd(b, a % b)
  rw [Nat.gcd_rec  (2 ^ (2 ^ n) + 1) (2 ^ (2 ^ m) + 1)]
  -- 用已知的条件重写表达式
  rw [power_mod_two_new]
  exact h

theorem pow_mod_two_zero_if_positive (n : ℕ) (h : 0 < n) : 2 ^ n % 2 = 0 := by
  rw [Nat.two_pow_mod_two_eq_zero]
  exact h

theorem gcd_power_two_one (n : ℕ) : Nat.gcd 2 (2 ^ (2 ^ n) + 1) = 1 := by
  -- rw [Nat.add_mod, Nat.mod_self, zero_add]
  -- exact Nat.even_pow x
  rw [Nat.gcd_rec 2 (2 ^ (2 ^ n) + 1)]
  have mod1: (2 ^ 2 ^ n) % 2 = 0 := by
    have ng1: 0 < n + 1 := by
      exact Nat.zero_lt_succ n
    have pow1 : 0 < 2 ^ n := by
      exact Nat.two_pow_pos n
    rw [Nat.two_pow_mod_two_eq_zero]
    exact pow1

  have mod2: (2 ^ 2 ^ n + 1) % 2 = 1 := by
    exact Nat.succ_mod_two_eq_one_iff.mpr mod1

  rw [mod2]
  exact rfl

-- #########################################
-- Here is the final Fermat gcd we want to show!!!!!
-- #########################################
-- #########################################
-- #########################################
-- #########################################
theorem finam_Fermat_gcd (m n : ℕ) (h : n < m):
  Nat.gcd (2 ^ (2 ^ n) + 1) (2 ^ (2 ^ m) + 1) = 1 := by
  rw [gcd_power_two, gcd_power_two_one]
  exact h


