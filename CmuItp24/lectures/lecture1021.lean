import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Heather Macbeth is giving a the Michalik Distinguished Lecture at the
University of Pittsburgh  in the Frick Fine Arts Building (room 125) on Friday at 3 PM:

  https://www.mathematics.pitt.edu/events/edmund-r-michalik-distinguished-lecture-series-mathematical-sciences-6

She is a leading expert on formalization, and the talk should be really interesting.

Kevin Buzzard will give a talk at CMU on December 6, 4-5 pm.

The first project will be due on Friday, November 8.

You have to turn in a start on the project on Friday, October 25,
for example, some definitions and a statement of a theorem you
intend to prove.

It won't be graded, but we will ask you to upload it to Gradescope (so we can provide feedback).

There is a blog post on probability theory in Mathlib:

  https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/

Today I will discuss an example from a lecture by Bhavik Mehta here:

  https://lftcm2023.github.io/tutorial/

There are other good tutorials there, and also on this page:

  https://leanprover-community.github.io/events.html

For the rest of the semester, the character of the class will change:

- Projects rather than weekly assignments.
- Informal discussions rather than lectures.

On Wednesday, we'll do introductions and I'll ask you to talk about your projects / interests.

There are still some topics I can lecture on:

- Lean's logical foundations.
- Filters and analysis.
- Linear algebra.
- Automation and Aesop.
- ...

# Recap

Last time, I talked about finsets and fintypes.

I'll pick ore on finite sets and cardinality.

-/

open Finset

section
variable {α : Type*} [DecidableEq α] (a : α) (s t u : Finset α)

-- Note the DecidableEq

#check a ∈ s
#check s ∩ t
#check s ∪ t
#check s \ t
#check (∅ : Finset α)

end

/-
Cardinality.
-/

#check card
#eval (range 5).card

example (s : Finset ℕ) : s.card = ∑ i ∈ s, 1 := by
  rw [card_eq_sum_ones]

example (s : Finset ℕ) : s.card = ∑ i ∈ s, 1 := by simp

/- The type-based analogue of a finset is a *fintype*. -/

section
variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := mem_univ

example : Fintype.card α = (Finset.univ : Finset α).card := rfl

example (n : ℕ) : Fintype.card (Fin n → α) = (Fintype.card α)^n := by
  simp

example (n : ℕ) : Fintype.card (Mathlib.Vector α n) = (Fintype.card α)^n := by
  simp

end

/-
Fintypes are closed under operations like the product operation.
-/

example : Fintype.card (Fin 5) = 5 := by simp
example : Fintype.card ((Fin 5) × (Fin 3)) = 15 := by simp

section
variable (s : Finset ℕ)

example : (↑s : Type) = {x : ℕ // x ∈ s} := rfl
example : Fintype.card ↑s = s.card := by simp
end

/-
Finite graphs with edges labeled by natural numbers.
-/

class NatLabeledDigraph (Vertex : Type*) where
  Edge : Type*
  finEdge : Fintype Edge
  source : Edge → Vertex
  target : Edge → Vertex
  capacity : Edge → ℕ

instance (Vertex : Type*) [NatLabeledDigraph Vertex] : Fintype (NatLabeledDigraph.Edge Vertex) :=
  NatLabeledDigraph.finEdge

section
open NatLabeledDigraph

variable {Vertex : Type*} [Fintype Vertex] [NatLabeledDigraph Vertex]
  [DecidableEq Vertex] [DecidableEq (Edge Vertex)]

variable (v1 v2 v3 : Vertex)
variable (e1 e2 e3 : Edge Vertex)

#check source e1
#check target e1
#check capacity e1

#check Finset.univ.filter fun e : Edge Vertex => source e = v1

def edgesFrom (v1 : Vertex) := Finset.univ.filter fun e : Edge Vertex => source e = v1

end

/-
Cardinality.
-/

#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint, card_range, card_image_of_injective,
    card_range]; ring
  . intro i1 i2; dsimp; omega
  rw [disjoint_iff_ne]
  simp
  intro a ha b _
  omega

example (n : ℕ) : card ((range (n+1) ×ˢ range (n+1)).filter (fun p => p.1 < p.2)) =
    n * (n + 1) / 2 := by
  have : (range (n+1) ×ˢ range (n+1)).filter (fun p => p.1 < p.2) =
    (range (n+1)).biUnion (fun j : ℕ => (range j).image fun i => (i, j)) := by
      sorry
  sorry
