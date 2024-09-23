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

We pretty much finished Chapter 4 (at least, 4.1 and 4.2. We'll skip 4.3 for now.)
-/


/-
The intermediate value theorem
-/


namespace IVT

def ApproachesAt (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - b| < ε

def Continuous (f : ℝ → ℝ) := ∀ x, ApproachesAt f (f x) x

variable (a b : ℝ) (f : ℝ → ℝ)

#check sSup
#check sSup { x : ℝ | a ≤ x ∧ x ≤ b ∧ f x ≤ 0 }
#check le_sSup
#check le_csSup
#check sSup_le
#check csSup_le

#print BddAbove
#print upperBounds

#check exists_lt_of_lt_csSup

theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : Continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 := by
  let S := { x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b }
  have zS : a ∈ S := by
    simp [S, le_of_lt hfa, aleb]
  have nonemptyS : S.Nonempty := ⟨a, zS⟩
  have bddS : BddAbove S := by
    use b
    intro x
    simp [S]
  let x₀ := sSup S
  have x₀gea : a ≤ x₀ := by
    apply le_csSup bddS zS
  have x₀leb : x₀ ≤ b := by
    apply csSup_le nonemptyS
    simp [S]
  have : ¬ f x₀ > 0
  · intro h
    rcases ctsf x₀ _ h with ⟨δ, δpos, hδ⟩
    have x₀pos : a < x₀
    · apply lt_of_le_of_ne x₀gea
      intro h'
      rw [←h'] at h
      exact lt_asymm hfa h
    have minpos : 0 < min (δ / 2) (x₀ - a) := by
      apply lt_min <;> linarith
    let x' := x₀ - min (δ / 2) (x₀ - a)
    have : ∃ x'' ∈ S, x' < x''
    · apply exists_lt_of_lt_csSup nonemptyS
      simp only [x', x₀]
      linarith
    rcases this with ⟨x'', x''S, x'lt⟩
    have : x'' ≤ x₀ := by
      exact le_csSup bddS x''S
    have : abs (f x'' - f x₀) < f x₀ := by
      apply hδ
      rw [abs_of_nonpos]
      have : min (δ / 2) (x₀ - a) < δ := by
        linarith [min_le_left (δ / 2) (x₀ - a)]
      have : x₀ < x' + δ := by
        simp [x']
        linarith
      linarith
      linarith
    rw [abs_lt] at this
    simp [S] at x''S
    linarith
  have : ¬ f x₀ < 0 := by
    intro h
    have : 0 < - f x₀ := by
      linarith
    rcases ctsf x₀ _ this with ⟨δ, δpos, hδ⟩
    have x₀lt1 : x₀ < b
    . apply lt_of_le_of_ne x₀leb
      intro h'
      rw [h'] at h
      exact lt_asymm hfb h
    have minpos : 0 < min (δ / 2) (b - x₀) := by
      apply lt_min <;> linarith
    let x' := x₀ + min (δ / 2) (b - x₀)
    have : abs (f x' - f x₀) < - f x₀ := by
      apply hδ
      simp [x']
      rw [abs_of_pos minpos]
      apply lt_of_le_of_lt (min_le_left _ _)
      linarith
    have x'S : x' ∈ S := by
      dsimp [S, x']
      rw [abs_lt] at this
      constructor; linarith
      constructor; linarith
      linarith [min_le_right (δ / 2) (b - x₀)]
    have : x' ≤ x₀ := le_csSup bddS x'S
    dsimp [x'] at this
    linarith
  have : f x₀ = 0 := by linarith
  use x₀, x₀gea, x₀leb, this

end IVT


section function_variables
open Function
variable {α : Type}

/-
There is a lot more in *Mathematics in Lean*.
There is a discussion of injectivity, more exercises on images and ranges,
and a discussion of inverses.

But we will close with on last exercise. Remember that `Surjective f`
says `∀ y, ∃ x, f x = y`.

-/

theorem Cantor {α : Type*} : ∀ f : α → Set α, ¬ Surjective f := by
  sorry

end function_variables

-- Nonterminal simps

section

variable {α : Type*} (A B : ℕ → Set α)

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) := by
  sorry

example (a b c d e f : ℕ) : a * ((b * c) * f * (d * e)) = d * (a * f * e) * (c * b) := by
  sorry

end

/-
Moving on to induction.
-/

def fac : ℕ → ℕ
| 0     => 1
| n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  sorry

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  sorry

theorem pow_two_le_fac (n : ℕ) : 2^(n-1) ≤ fac n := by
  sorry

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x in s, f x := rfl
example : s.prod f = ∏ x in s, f x := rfl

example : (range n).sum f = ∑ x in range n, f x := by
  sorry

example : (range n).prod f = ∏ x in range n, f x := by
  sorry

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 := by
  sorry

example (f : ℕ → ℕ) (n : ℕ): ∑ x in range n.succ, f x = (∑ x in range n, f x) + f n := by
  sorry

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 := by
  sorry

example (f : ℕ → ℕ) (n : ℕ): ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n := by
  sorry

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  sorry

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  sorry

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 := by
  sorry

end

inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat

namespace my_nat

def add : my_nat → my_nat → my_nat
| x, zero   => x
| x, succ y => succ (add x y)

def mul : my_nat → my_nat → my_nat
| x, zero   => zero
| x, succ y => add (mul x y) x

theorem zero_add (n : my_nat) : add zero n = n := by
  sorry

theorem succ_add (m n : my_nat) : add (succ m) n = succ (add m n) := by
  sorry

theorem add_comm (m n : my_nat) : add m n = add n m := by
  sorry

theorem add_assoc (m n k : my_nat) : add (add m n) k = add m (add n k) := by
  sorry

theorem mul_add  (m n k : my_nat) : mul m (add n k) = add (mul m n) (mul m k) := by
  sorry

theorem zero_mul (n : my_nat) : mul zero n = zero := by
  sorry

theorem succ_mul (m n : my_nat) : mul (succ m) n = add (mul m n) n := by
  sorry

theorem mul_comm (m n : my_nat) : mul m n = mul n m := by
  sorry

end my_nat
