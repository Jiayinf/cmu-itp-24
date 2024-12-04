import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic


-- Definitions
def is_mersenne (n : ℕ) : Prop :=
  ∃ q : ℕ, Nat.Prime q ∧ n = 2^q - 1

def is_wieferich_prime (p : ℕ) : Prop :=
  Nat.Prime p ∧ (2^(p - 1)) % (p^2) = 1

def is_not_squarefree (n : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ p^2 ∣ n

-- Theorem: If a Mersenne number is not squarefree, then it must be divisible by a Wieferich prime.
theorem mersenne_not_squarefree_iff_wieferich_prime :
  ∀ n : ℕ, is_mersenne n → is_not_squarefree n → ∃ p : ℕ, is_wieferich_prime p ∧ p ∣ n := by

  intros n hnM hnSQ
  rcases hnM with ⟨q, hq_prime, hq_eq⟩
  rcases hnSQ with ⟨p, hp_prime, hdiv⟩
  use p
  refine ⟨⟨hp_prime, _⟩, _⟩
  · -- Show that p is a Wieferich prime
    have hpow : 2^(q - 1) ≡ 1 [MOD p^2] := by
      rw [←hq_eq]
      apply Nat.ModEq.pow
      rw [Nat.Prime.dvd_mul_left_iff]
      exact hdiv
    exact hpow
  · -- Show that p divides n
    rw [hq_eq]
    exact Nat.Prime.dvd_of_pow_dvd hdiv
    sorry

theorem triple_split (a b: ℤ) : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by
    rw [Int.mul_add, Int.mul_add]
    rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]
    rw [←Int.mul_assoc, ←Int.mul_assoc]
    rw [Int.add_assoc, ←Int.add_sub_assoc, pow_two]
    simp [pow_succ, ←mul_assoc]
    linarith



theorem int_diff_squares_iff_not_4k_plus_2 (n : ℤ) :
  (∃ a b : ℤ, n = a^3 - b^3) ↔ ¬ ∃ k : ℤ, n = 4 * k + 2 := by
  have h1 : (∃ a b : ℤ, n = (a - b) * (a^2 + a * b + b^2)) := by
    apply Exists.elim

    use [a, b]
    exact ⟨a, b, by rw [triple_split a b]⟩
