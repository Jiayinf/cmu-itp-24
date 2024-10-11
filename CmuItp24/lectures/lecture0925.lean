import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 5 is online.

Plan:

- This week: induction, algebraic structures
- Next two weeks: more algebra, discrete math, tour of Mathlib

- Fall break!

- First project (3 weeks)
- Second project (4 weeks)

# Recap

We're done with Chapter 4.

# Agenda

We'll do Section 5.2 on induction and recursion, and then start talking about algebraic
structures.

-/

/-
A problem from homework 3:
-/

def ApproachesAt (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

theorem approachesAt_comp {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : ApproachesAt f b a) (hg : ApproachesAt g c b) :
    ApproachesAt (g ∘ f) c a := by
  intro ε εpos
  rcases hg ε εpos with ⟨δ', δ'pos, hδ'⟩
  rcases hf δ' δ'pos with ⟨δ, δpos, hδ⟩
  use δ, δpos
  intro x hx
  apply hδ'
  exact hδ _ hx

/-
Moving on to induction.
-/

def fac : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fac n

#eval fac 6
#eval fac 10

section
variable (x : ℕ)

example : fac 0 = 1 := rfl
example : fac 0 = 1 := by rw [fac]
example : fac 0 = 1 := by simp [fac]

example : fac (x + 1) = (x + 1) * fac x := rfl
example : fac (x + 1) = (x + 1) * fac x := by rw [fac]

end

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  . rw [fac]; norm_num
  . rw [fac]
    apply mul_pos
    . simp
    . assumption

example (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  . rw [fac]; norm_num
  rw [fac]
  apply mul_pos
  . simp
  . assumption

example (n : ℕ) : 0 < fac n := by
  induction n with
  | zero => rw [fac]; norm_num
  | succ n ih =>
      rw [fac]
      apply mul_pos
      . simp
      . assumption

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  . -- have := not_lt_of_ge ile
    -- contradiction
    linarith
  rw [fac]
  rcases lt_or_eq_of_le ile with h | h
  . apply dvd_mul_of_dvd_right
    apply ih
    omega -- or linarit
  . apply dvd_mul_of_dvd_left
    rw [h]

theorem pow_two_le_fac (n : ℕ) : 2^(n-1) ≤ fac n := by
  rcases n with _ | n
  . simp [fac]
  simp only [add_tsub_cancel_right]
  induction' n with n ih
  . simp [fac]
  rw [fac, pow_succ']
  -- apply?
  apply Nat.mul_le_mul _ ih
  simp -- linarith
