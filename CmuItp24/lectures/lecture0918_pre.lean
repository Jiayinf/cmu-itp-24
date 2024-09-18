import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 4 is in the repository.

# Recap

We started Chapter 4, talking about sets. (See below.)

# Agenda

More on sets and functions.

-/

/-
Name that theorem!
-/

namespace strictMono_exercise

variable (f : ℝ → ℝ) (g : ℝ → ℝ)

example (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f + g) := by
  sorry

example (c : ℝ) (hf : StrictMono f) (hc : 0 < c) :
    StrictMono (fun x => c * f x) := by
  sorry

example (hf : StrictMono f) : Monotone f := by
  sorry

open Function

example (hf : StrictMono f) : Injective f := by
  sorry

end strictMono_exercise

/-
Recap of set notation and operations.
-/

open Set Nat Function

variable {α : Type*} {β : Type*} {γ : Type*} {I : Type*}

section set_variables

variable (x : α)
variable (s t u : Set α)


#check s ⊆ t        -- \sub
#check x ∈ s        -- \in or \mem
#check x ∉ s        -- \nin
#check s ∩ t        -- \i or \cap
#check s ∪ t        -- \un or \cup
#check (∅ : Set α)  -- \empty
#check (univ : Set α)

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

example : s ∩ s = s := by
  sorry

/-
Set-builder notation
-/

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  sorry

example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := rfl
example : (∅ : Set α) = {x | False} := rfl
example : (univ : Set α) = {x | True} := rfl

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  sorry

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  sorry

-- Use the theorem ``Prime.eq_two_or_odd``

#check Prime.eq_two_or_odd

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry

/-
Bounded quantifiers
-/

section

variable (s t : Set ℕ) (P : ℕ → Prop)

example (h : ∀ x ∈ t, P x) : ∀ x ∈ s ∩ t, P x := by
  sorry

end

/-
Indexed unions
-/

section

-- We can use any index type in place of ℕ
variable (A B : ℕ → Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  sorry

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry

-- One direction requires classical logic!
-- Use ``by_cases xs : x ∈ s``
-- at an appropriate point in the proof.

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

end

/-
Mathlib also has bounded unions and intersections,
`⋃ x ∈ s, f x` and `⋂ x ∈ s, f x`,
and set unions and intersections, `⋃₀ s` and `⋂₀ s`,
where `s : set α`.
-/

end set_variables

/-
# Functions
-/

section function_variables

variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)
variable (A : I → Set α)
variable (B : I → Set β)

#check f '' s
#check image f s
#check f ⁻¹' u    -- type as \inv' and then hit space or tab
#check preimage f u

example : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl
example : f ⁻¹' u = {x | f x ∈ u} := rfl

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  sorry

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  sorry

example : s ⊆ f ⁻¹' (f '' s) := by
  sorry

/-
Exercises
-/

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
sorry

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s :=
sorry

example : f '' (f⁻¹' u) ⊆ u :=
sorry

example (h : Surjective f) : u ⊆ f '' (f⁻¹' u) :=
sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
sorry

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
sorry

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
sorry

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
sorry

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
sorry

end function_variables
