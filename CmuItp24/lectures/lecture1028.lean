import Mathlib.Data.Real.Basic
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

We will provide feedback on your initial submission soon.

- We are planning to send messages via Piazza.
- Please don't hesitate to ask questions.

Soon we will bump `cmu-itp-24` to a newer version of Mathlib. We'll announce it on Piazza.
After that, the next time you update the repository, use

  `lake exe cache get`

to fetch the newer precompiled Mathlib.

I will be traveling Tuesday to Thursday next week; Wojciech will lecture instead.

# Agenda

Probability theory.

See: https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/

Coming up: filters and limits.

-/

/-
For finite spaces, we can use a probability mass functions.
-/

class FinitePMF' (α : Type) [Fintype α] where
  prob : α → ℝ
  prob_nonneg : ∀ x, 0 ≤ prob x
  sum_prob_eq_one : ∑ x : α, prob x = 1

section

variable {α : Type} [Fintype α] [DecidableEq α] [FinitePMF' α]

open FinitePMF' Finset

example : ∀ x : α, prob x ≤ 1 := by
  intro x
  have : prob x + ∑ y ∈ univ.erase x, prob y = 1 := by
    rw [←sum_prob_eq_one (α := α), ←sum_singleton prob x, ←sum_union,
      ←insert_eq, insert_erase] <;> simp
  have : 0 ≤ ∑ y ∈ univ.erase x, prob y := by
    apply sum_nonneg
    intro z _
    apply prob_nonneg
  linarith

end

/-
That option presupposes there is a single probability associated with α. Another option
is to make it explicit.
-/

structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  prob_nonneg : ∀ x, 0 ≤ prob x
  sum_prob_eq_one : ∑ x : α, prob x = 1

-- we define a coercion which lets us write `p x` instead of `p.prob x`.

instance {α : Type*} [Fintype α] : CoeFun (FinitePMF α) (fun _ => α → ℝ) :=
  ⟨fun p => p.prob⟩

namespace FinitePMF

variable {α : Type} [Fintype α] [DecidableEq α] (p : FinitePMF α)

open Finset

theorem prob_le_one : ∀ x : α, p x ≤ 1 := by
  intro x
  have : p x + ∑ y ∈ univ.erase x, p y = 1 := by
    rw [←p.sum_prob_eq_one, ←sum_singleton p x, ←sum_union,
      ←insert_eq, insert_erase] <;> simp
  have : 0 ≤ ∑ y ∈ univ.erase x, p y := by
    apply sum_nonneg
    intro z _
    apply prob_nonneg
  linarith

end FinitePMF

/-
Yet another option is to make the function a parameter of the class.
-/

class FinitePMF'' {α : Type} [Fintype α] (p : α → ℝ) where
  prob_nonneg : ∀ x, 0 ≤ p x
  sum_prob_eq_one : ∑ x : α, p x = 1

section

variable {α : Type} [Fintype α] (p : α → ℝ) [FinitePMF'' p]

open FinitePMF''

example (x : α) : 0 ≤ p x := by
  sorry

end

/-
Another approach, which gets us closer to infinitary probability, is to define
a probability as a function that maps any subset of α to a real number between 0 and 1.
-/

structure FiniteProbability (α : Type*) [Fintype α] [DecidableEq α] where
  prob : Finset α → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_univ : prob Finset.univ = 1
  prob_union_of_disjoint : ∀ s t, Disjoint s t → prob (s ∪ t) = prob s + prob t

instance {α : Type*} [Fintype α] [DecidableEq α] :
    CoeFun (FiniteProbability α) (fun _ => Finset α → ℝ) :=
  ⟨fun P => P.prob⟩

namespace FinitePMF
variable {α : Type*} [Fintype α] [DecidableEq α]
open Finset

-- Every `FinitePMF` gives rise to a finite probability.

def toFiniteProbability  (p : FinitePMF α) : FiniteProbability α where
  prob := fun s => ∑ x ∈ s, p x
  prob_nonneg := by
    intro s; dsimp
    apply sum_nonneg
    intro z _
    apply p.prob_nonneg
  prob_univ := p.sum_prob_eq_one
  prob_union_of_disjoint := by
    intro s t hdisj; dsimp
    rw [sum_union hdisj]

end FinitePMF

-- We can now reason axiomatically about finite probability spaces.

namespace FiniteProbability

variable {α : Type} [Fintype α] [DecidableEq α] (P : FiniteProbability α)
variable (s t : Finset α)

#check P (s ∪ t)

example :  P s + P sᶜ = 1 := by
  rw [←prob_union_of_disjoint, Finset.union_compl, prob_univ]
  rw [@Finset.disjoint_iff_inter_eq_empty]; simp

end FiniteProbability

/-
In general, we can assign probabilities to an infinite space. If we only care about
finite additivity, we just replace `Finset` with `Set`.
-/

structure FinitelyAdditiveProbability (α : Type*) where
  prob : Set α → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_univ : prob Set.univ = 1
  prob_union_of_disjoint : ∀ s t, Disjoint s t → prob (s ∪ t) = prob s + prob t

instance {α : Type*}  :
    CoeFun (FinitelyAdditiveProbability α) (fun _ => Set α → ℝ) :=
  ⟨fun P => P.prob⟩

section FinitelyAdditiveProbability

variable {α : Type*} (P : FinitelyAdditiveProbability α)

variable (s t : Set α)

#check P (s ∪ t)

theorem prob_add_prob_compl :  P s + P sᶜ = 1 := by
  rw [←P.prob_union_of_disjoint, Set.union_compl_self, P.prob_univ]
  rw [Set.disjoint_iff_inter_eq_empty]; simp

theorem prob_le_one (s : Set α) : P s ≤ 1 := by
  rw [←prob_add_prob_compl]
  linarith [P.prob_nonneg sᶜ]

end FinitelyAdditiveProbability

/-
Suppose we want to deal with infinite, discrete spaces. We can still use a PMF, but
we now need infinite sums.

Note that even if the space is uncountably infinite, if the PMF sums to 1,
only countably many elements have positive probability.

In general, infinite sums can take values in the extended nonnegative reals, so the
mechanisms for handing infinite sums take values there.
-/

open scoped ENNReal

#check tsum
#print PMF
#print HasSum

section

#check ENNReal
#check ℝ≥0∞

variable (a b c : ℝ≥0∞)

example : a + b = b + a := by sorry

example : a + 2 + 3 = a + 5 := by sorry

example : a + b + c = a + (b + c) := by sorry

#check a.toReal

example (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
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

open MeasureTheory

#print Measure

example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s

/-
A probabilisty measure is just a measure that gives the universe measure 1.
-/

open ProbabilityTheory

#print IsProbabilityMeasure

section

variable {P : Measure ℝ} [IsProbabilityMeasure P]

example (s : Set ℝ) : P s ≠ ∞ := by
  simp

example (s t : Set ℝ) (h : Disjoint s t) (h' : MeasurableSet t): P (s ∪ t) = P s + P t := by
  sorry

end

section

variable {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

#check MeasurableSet.of_discrete

example (s t : Set Ω) (h : Disjoint s t) : P (s ∪ t) = P s + P t := by
  sorry

end
