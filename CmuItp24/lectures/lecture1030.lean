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
Wednesday, 11-12 (Wojciech)
Wednesday, 3:30-4:30 (Eric)
Thursday, 11-12 (Wojciech)
Thursday, 4-5 (Eric)
Friday, 10-11 (Jeremy)

# Agenda

Various comments.

Filters and limits.

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

#check Fintype.card α
#check (Finset.univ : Finset α)
#check ∑ x : α, f x

end

/-
subtypes
-/

section

variable (P : ℕ → Prop)

#check {x | P x}
#check {x // P x}
#check {x : ℕ // P x}

example (y : {x // P x}) : P y := by
  have a := y.1
  have h := y.2
  let n := (y : ℕ)
  apply y.2

variable (s : Set ℕ)

#check (s : Type)

example : (s : Type) = {x : ℕ // x ∈ s} := rfl

variable {α : Type}

#check (Set.univ : Set α)

end

/-
strong induction
-/

section

variable (P : ℕ → Prop) (h : ∀ x, (∀ y < x, P y) → P x)

example : ∀ x, P x := by
  suffices ∀ y, ∀ z < y, P z by
    intro x
    apply this (x + 1) x; simp
  intro y
  induction' y with y ih
  . simp -- tauto
  intro z
  rw [Nat.lt_succ_iff_lt_or_eq]
  rintro (h' | rfl)
  . apply ih _ h'
  apply h _ ih

example : ∀ x, P x := by
  intro x
  induction' x using Nat.strongRecOn with x ih
  apply h _ ih

include h
theorem foo : ∀ x, P x
  | _ => by
      apply h
      intro y _
      apply foo

end

/-
On ℕ, subtraction is a pain in the neck. On ℕ and ℤ, division is a pain in the neck.
-/

example (a b c : ℕ) (h : a = b + c) : a - b = c := by
  -- exact?
  -- exact Eq.symm (Nat.eq_sub_of_add_eq' (id (Eq.symm h)))
  symm
  apply Nat.eq_sub_of_add_eq'
  rw [h]

example (a b c : ℤ) (h: a = b * c) (h' : b ≠ 0) : a / b = c := by
  -- exact?
  exact Eq.symm (Int.eq_ediv_of_mul_eq_right h' (id (Eq.symm h)))

/-
Matrices
-/

#check Matrix

section

variable {u v : Type*} [Fintype u] [Fintype v]
variable (m n : ℕ)

#check Matrix (Fin n) (Fin m) ℤ
#check Fin n → ℤ

#check Matrix u v ℤ
#check u → ℤ

example (h : 0 < n) (x : Fin n) : x = x := rfl

def foo' (h : 0 < n) (v : Fin n → ℤ) : ℤ := v ⟨0, h⟩

def foo'' (vec : Fin (n + 1) → ℤ) := vec 0

variable [Inhabited u]

#check (default : u)

def foo''' (vec : u → ℤ) : ℤ := vec default

end

/-
Using filters.
-/

section
open Filter

variable (f g : ℝ → ℝ) (a b a' b' : ℝ)

example : Tendsto f (nhds a) (nhds b) := by
  rw [@Metric.tendsto_nhds_nhds]
  simp_rw [dist]
  sorry

example : Tendsto f atTop (nhds b) := by
  sorry

example (h1 : Tendsto f atTop (nhds a)) (h2 : Tendsto g atTop (nhds b)) :
    Tendsto (fun x ↦ f x + g x) atTop (nhds (a + b)) := by
  -- apply?
  apply Tendsto.add h1 h2

variable (F₁ F₂ : Filter ℝ)

example : Tendsto f F₁ F₂ := by
  sorry

end
