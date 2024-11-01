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

Instead of class next week, Wojciech will hold an extra office hour.

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
  sorry

end

/-
Another combinatorial example.
-/

section
open Finset Classical

#check Finset.sum_boole

/-
The example from Bhavik's lecture:
-/

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
  (r : α → β → Prop)
  (h_left : ∀ a ∈ s, 3 ≤ card (t.filter (r a ·)))
  (h_right : ∀ b ∈ t, card (s.filter (r · b)) = 1) :
    3 * s.card ≤ t.card := by
  calc
    3 * s.card ≤ ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by sorry
    _ ≤ t.card := by sorry


/-
An exercise from Bhavik. Also: replace = by ≤ in the previous theorem.
-/

theorem Nat.coprime_self_add_one (n : ℕ) : Nat.Coprime n (n + 1) := by
  simp only [coprime_self_add_right, coprime_one_right_eq_true]

example {n : ℕ} (A : Finset ℕ)
  (hA : A.card = n + 1)
  (hA' : A ⊆ Finset.range (2 * n)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ Nat.Coprime x y := by
sorry

end

/-
Back to probability theory.

Remember what we did in the finite case:
-/

structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  prob_nonneg : ∀ x, 0 ≤ prob x
  sum_prob_eq_one : ∑ x : α, prob x = 1

structure FiniteProbability (α : Type*) [Fintype α] [DecidableEq α] where
  prob : Finset α → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_univ : prob Finset.univ = 1
  prob_union_of_disjoint : ∀ s t, Disjoint s t → prob (s ∪ t) = prob s + prob t

/-
Suppose we want to deal with infinite, discrete spaces. We can still use a PMF, but
we now need infinite sums.

Note that even if the space is uncountably infinite, if the PMF sums to 1,
only countably many elements have positive probability.

In general, infinite sums can take values in the extended nonnegative reals, so the
mechanisms for handing infinite sums take values there.
-/

section
open scoped ENNReal

#check tsum
#print PMF
#print HasSum

#check ENNReal
#check ℝ≥0∞

variable (a b c : ℝ≥0∞)

example : a + b = b + a := by sorry

example : a + 2 + 3 = a + 5 := by sorry

example : a + b + c = a + (b + c) := by sorry

#check a.toReal

example (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
  sorry

-- ENNReal still has a semiring structure
example (x y : ENNReal) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  sorry

example : (1 : ENNReal) + 4 = 5 := by
  sorry

example (x y z w : ENNReal) (h1 : x < y) (h2 : z ≤ w) :
    x + z < y + w := by
  sorry

end

/-
In full, measure theory, things get more complicated:

- The measure of a set might be infinite (so the theory uses `ENNReal` numbers.)

- There is an axiom that says that the measure of a disjoint union of countable sets
  is equal to the sum of the measures of each one.

- Not every set is measurable (so the theory used the notions of a measurable space
  and measurable sets.)
-/

section
open MeasureTheory Set ENNReal

variable {α : Type*} [MeasurableSpace α]

example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

variable {ι : Type*} [Encodable ι]

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  sorry

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  sorry

variable {μ : Measure α}

example (s : Set α) : ℝ≥0∞ := μ s

example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  sorry

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  sorry

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  sorry

example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
  sorry

end

/-
A probability measure is just a measure that gives the universe measure 1.
-/

section
open ProbabilityTheory MeasureTheory ENNReal

#print IsProbabilityMeasure

variable {P : Measure ℝ} [IsProbabilityMeasure P]

example (s : Set ℝ) : P s ≠ ∞ := by
  sorry

example (s t : Set ℝ) (h : Disjoint s t) (h' : MeasurableSet t): P (s ∪ t) = P s + P t := by
  sorry

variable {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

#check MeasurableSet.of_discrete

example (s t : Set Ω) (h : Disjoint s t) : P (s ∪ t) = P s + P t := by
  sorry

end
