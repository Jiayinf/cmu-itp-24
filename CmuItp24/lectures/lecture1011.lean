import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

The first project will be due on Friday, November 8.

You have to turn in a start on the project on Friday, October 25,
for example, some definitions and a statement of a theorem you
intend to prove.

# Recap

- finished talking about algebraic structures (for now)
- talked about the final project

# Today

- a quick look at Mathlib
- finite sets and structures
-/

section
variable {α : Type*} [DecidableEq α] (a : α) (s t u : Finset α)

-- Note the DecidableEq

#check a ∈ s
#check s ∩ t
#check s ∪ t
#check s \ t
#check (∅ : Finset α)

open Finset

example : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x; simp; tauto

#check ({0, 2, 5} : Finset Nat)

example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by
  decide

example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by
  ext x; simp; tauto

example : ({0, 1, 2} : Finset ℕ) = {0, 1, 1, 2} := by
  simp

example : ({0, 1} : Finset ℕ) = {1, 0} := by
  rw [pair_comm]

example (x : Nat) : ({x, x} : Finset ℕ) = {x} := by simp

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  -- decide
  ext x
  simp [or_comm, or_assoc, or_left_comm]

example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s |>.erase a) = s :=
  -- by simp [*]
  Finset.erase_insert h

example (s : Finset ℕ) (a : ℕ) (h : a ∈ s) : insert a (s.erase a) = s :=
  Finset.insert_erase h

set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)

open Finset
variable (n : ℕ)

#check (range n).filter Even
#check (range n).filter (fun x ↦ Even x ∧ x ≠ 4)

#eval (range 10).filter (fun x ↦ Even x ∧ x ≠ 4)

example : (range 10).filter Even = {0, 2, 4, 6, 8} := by decide

#check (range 5).image fun x ↦ x^2
#eval (range 5).image fun x ↦ x^2

example : (range 5).image (fun x ↦ x * 2) = (range 10).filter Even := by decide

section
variable (s t : Finset Nat)
#check s ×ˢ t

#eval {0, 1, 2} ×ˢ ({2, 4, 6} : Finset ℕ)
#check s.powerset

#eval (range 5).powerset

end

section
#check Finset.fold

def f (n : ℕ) : Int := (↑n)^2

#check (range 5).fold (fun x y : Int ↦ x + y) 0 f
#eval (range 5).fold (fun x y : Int ↦ x + y) 0 f

#check ∑ i ∈ range 5, i^2
#check ∏ i ∈ range 5, i + 1

variable (g : Nat → Finset Int)

#check (range 5).biUnion g

end

/-
There is a natural principle of induction on finsets: to prove that every finset
has a property, show that the empty set has the property and that the property is
preserved when we add one new element to a finset. (The ``@`` in ``@insert`` is need
in the induction step to give names to the parameters ``a`` and ``s`` because they
have been marked implicit. )
-/

#check Finset.induction

example {α : Type*} [DecidableEq α] (f : α → ℕ)  (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s anins ih =>
      -- simp [*]
      rw [prod_insert]
      apply mul_ne_zero
      . apply h; simp
      apply ih
      intro x xs
      apply h
      -- apply?
      · exact mem_insert_of_mem xs
      exact anins

noncomputable example (s : Finset ℕ) (h : s.Nonempty) : ℕ := Classical.choose h

example (s : Finset ℕ) (h : s.Nonempty) : Classical.choose h ∈ s :=
   Classical.choose_spec h

noncomputable example (s : Finset ℕ) : List ℕ := s.toList

example (s : Finset ℕ) (a : ℕ) : a ∈ s.toList ↔ a ∈ s := mem_toList

#eval Finset.min {1, 2, 4}
#eval Finset.min (∅ : Finset ℕ)

#check Finset.min
#check Finset.min'
#check Finset.max
#check Finset.max'
#check Finset.inf
#check Finset.inf'
#check Finset.sup
#check Finset.sup'

example : Finset.Nonempty {2, 6, 7} := ⟨6, by trivial⟩
example : Finset.min' {2, 6, 7} ⟨6, by trivial⟩ = 2 := by trivial

/-
Cardinality.
-/

#check Finset.card
#eval (range 5).card
#eval (range 20).filter Even |>.card

example (s : Finset ℕ) : s.card = ∑ i ∈ s, 1 := by
  rw [card_eq_sum_ones]

/- The type-based analogue of a finset is a *fintype*. -/

section
variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := mem_univ

-- #check (Finset.univ : Finset ℕ)

example : Fintype.card α = (Finset.univ : Finset α).card := rfl
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

end
