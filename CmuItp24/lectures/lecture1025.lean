import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-
# Announcements

Heather Macbeth is giving a the Michalik Distinguished Lecture at the
University of Pittsburgh in the Frick Fine Arts Building (room 125) at 3:30 PM
(doors open at 3):

  https://www.mathematics.pitt.edu/events/edmund-r-michalik-distinguished-lecture-series-mathematical-sciences-6

She is a leading expert on formalization, and the talk should be really interesting.

The first project will be due on Friday, November 8.

You have to turn in a start on the project today on Gradescope.


# Agenda

Axiom of choice.

More combinatorics.

Probability theory.
-/

/-
Choice:
-/

#check Classical.choose
#check Classical.choose_spec

-- open Classical

example {α β : Type*} (R : α → β → Prop) :
    (∀ x : α, ∃ y : β, R x y) → ∃ f : α → β, ∀ x, R x (f x) := by
  intro h
  use fun x => Classical.choose (h x)
  intro x
  apply Classical.choose_spec

example {α β : Type*} (R : α → β → Prop) :
    (∀ x : α, ∃ y : β, R x y) → ∃ f : α → β, ∀ x, R x (f x) := by
  intro h
  choose f hf using h
  use f, hf

example {α β : Type*} (R : α → β → Prop) :
    (∀ x : α, ∃ y : β, R x y) → ∃ f : α → β, ∀ x, R x (f x) := by
  choose f hf
  use f, hf

/-
Cardinality.
-/

section
open Finset
#check Disjoint

example (m n : ℕ) (h : m ≥ n) : card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint]
  · rw [card_range, card_image_of_injective]
    · rw [card_range]; omega
    apply add_right_injective
  rw [disjoint_iff_ne]
  simp; intro i j; omega

#eval ((range (5+1) ×ˢ range (5+1)).filter (fun p => p.1 < p.2))

example (n : ℕ) : card ((range (n+1) ×ˢ range (n+1)).filter (fun p => p.1 < p.2)) =
    n * (n + 1) / 2 := by
  have : (range (n+1) ×ˢ range (n+1)).filter (fun p => p.1 < p.2) =
    (range (n+1)).biUnion (fun j : ℕ => (range j).image fun i => (i, j)) := by
      ext p
      simp [Prod.ext_iff]
      constructor
      . rintro ⟨⟨_, h2⟩, h3⟩
        use p.2, h2, p.1
      . rintro ⟨p1, h1, p2, h2⟩
        omega
  rw [this, Finset.card_biUnion]
  swap
  . intro i hi j hj ijne
    rw [disjoint_iff_ne]
    simp
    tauto
  trans ∑ u ∈ range (n + 1), u
  congr; ext u
  rw [card_image_of_injective]
  . simp
  . intro i1 i2 h'
    simpa using h'
  rw [sum_range_id, mul_comm]; simp
