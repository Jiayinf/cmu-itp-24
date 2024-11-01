import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
import Mathlib.Probability.Integration
import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-
# Announcements

The first project is due on Friday, November 8.

I will be traveling Tuesday to Thursday next week.

Instead of class next Wednesday, Wojciech will hold an extra office hour.

Office hours for next week:

Monday, 2-3 (Jeremy)
Wednesday, 11-1 (Wojciech) -- note, two hours!
Wednesday, 3:30-4:30 (Eric)
Thursday, 11-12 (Wojciech)
Thursday, 4-5 (Eric)
Friday, 10-11 (Jeremy)

Next week: dependent type theory and Lean's axiomatic foundation.

# Agenda

Another combinatorial example.

Measure theory (following MIL).

Probability theory.

See: https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/

-/

/-
An annoying example:
-/

section
variable {α : Type*} [DecidableEq α] (A1 A2 : Finset α)

open Finset

example (h1 : A1 ⊆ A2) (h2 : A1.card < A2.card) :
    ∃ x ∈ A2, x ∉ A1 := by
  refine not_subset.mp ?_
  intro h3
  have : A1 = A2 := by
    exact Subset.antisymm h1 h3
  subst this
  simp at h2

example (h1 : A1 ⊆ A2) (h2 : A1.card < A2.card) :
    ∃ x ∈ A2, x ∉ A1 := by
  apply Finset.exists_of_ssubset
  rw [@Finset.ssubset_iff_subset_ne]
  use h1
  contrapose! h2
  rw [h2]

end

/-
Another combinatorial example.
-/

section
open Finset Classical

#check Finset.sum_boole

/-
The example from Bhavik Mehta's lecture:
-/

#check fun x => x + 3
#check (· + 3)
#check (. + 3)

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
  (r : α → β → Prop)
  (h_left : ∀ a ∈ s, 3 ≤ card (t.filter (r a ·)))
  (h_right : ∀ b ∈ t, card (s.filter (r · b)) = 1) :
    3 * s.card ≤ t.card := by
  calc 3 * s.card
      = ∑ a ∈ s, 3 := by simp_arith
    _ ≤ ∑ a ∈ s, card (t.filter (r a ·)) := by
          exact sum_le_sum h_left
    _ ≤ ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := by rw [sum_comm]
    _ = ∑ b ∈ t, 1 := by
      apply sum_congr rfl
      intro x hx; simp [h_right x hx]
    _ = t.card := by simp

/-
An exercise from Bhavik.
-/

theorem Nat.coprime_self_add_one (n : ℕ) : Nat.Coprime n (n + 1) := by
  simp only [coprime_self_add_right, coprime_one_right_eq_true]

example {n : ℕ} (A : Finset ℕ)
  (hA : A.card = n + 1)
  (hA' : A ⊆ Finset.range (2 * n)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ Nat.Coprime x y := by
sorry

end
