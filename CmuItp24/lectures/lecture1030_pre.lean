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

We are working on giving you feedback.

- We are sending messages via Piazza.
- Please don't hesitate to ask questions.

We bumped `cmu-itp-24` to a newer version of Mathlib. If you haven't already, use

  `lake exe cache get`

to fetch the newer precompiled Mathlib next time you pull the repository.

I will be traveling Tuesday to Thursday next week; Wojciech will lecture instead.
(Or, possibly, we will replace class by an office hour.)

Office hours for next week:

Monday, 2-3 (Jeremy)
Wedneday, 11-12 (Wojciech)
Wednesday, 3:30-4:30 (Eric)
Thursday, 11-12 (Wojciech)
Thursday, 4-5 (Eric)
Friday, 10-11 (Jeremy)

# Agenda

Various comments.

Filters and limits.

Probability theory.

See: https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/

-/

/-
Dealing with finiteness:

- Use an arbitrary type and finsets:

variable {α : Type*} [DecidableEq α] (s t : Finset α)

- Use a fintype and finsets:

variable {α : Type*} [DecidableEq α] [Fintype α] (s t : Finset α)

It's the same thing, except you can use `(Finset.univ : Finset α)` and
`Fintype.card α` and `∑ x : α, f x`.
-/

section

variable {α : Type*} [DecidableEq α] [Fintype α] (s t : Finset α)
variable (f : α → ℝ)

end

/-
strong induction
-/

section

variable (P : ℕ → Prop) (h : ∀ x, (∀ y < x, P y) → P x)

example : ∀ x, P x := by
  sorry

end

/-
On ℕ, subtraction is a pain in the neck. On ℕ and ℤ, division is a pain in the neck.
-/

example (a b c : ℕ) (h : a = b + c) : a - b = c := by
  sorry

example (a b c : ℤ) (h: a = b * c) (h' : b ≠ 0) : a / b = c := by
  sorry

/-
Matrices
-/

#check Matrix

section

variable {u v : Type*} [Fintype u] [Fintype v]
variable (m n : ℕ)

end

/-
Using filters.
-/

section
open Filter

variable (f g : ℝ → ℝ) (a b a' b' : ℝ)

example : Tendsto f (nhds a) (nhds b) := by
  sorry

example : Tendsto f atTop (nhds b) := by
  sorry

example (h1 : Tendsto f atTop (nhds a)) (h2 : Tendsto g atTop (nhds b)) :
    Tendsto f atTop (nhds (a + b)) := by
  sorry

variable (F₁ F₂ : Filter ℝ)

example : Tendsto f F₁ F₂ := by
  sorry

end

/-
Another combinatorial example.
-/

section
open Finset Classical

variable {α β : Type*}

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
  (r : α → β → Prop)
  (h_left : ∀ a ∈ s, 3 ≤ card (t.filter (r a ·)))
  (h_right : ∀ b ∈ t, card (s.filter (r · b)) = 1) :
    3 * s.card ≤ t.card := by
  calc
    3 * s.card ≤ ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by sorry
    _ ≤ t.card := by sorry

end
