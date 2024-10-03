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

theorem strictMono_add (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f + g) := by
  sorry

-- could add "of_pos" if needed
theorem strictMono_mul_left (c : ℝ) (hf : StrictMono f) (hc : 0 < c) :
    StrictMono (fun x => c * f x) := by
  sorry

theorem monotone_of_strictMono  (hf : StrictMono f) : Monotone f := by
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
  intro x ⟨⟨xs, xnt⟩, xnu⟩
  constructor
  . assumption
  . -- simp [*] at *
    rintro (xt | xu) <;> contradiction

example : s ∩ s = s := by
  ext y
  simp

/-
Set-builder notation
-/

def evens : Set ℕ :=
  { n | Even n }

#check Even
#check evens

example (x : ℕ) (h : Even x) : x ∈ evens :=
  h

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  ext x
  --rw [evens, odds, mem_union]
  --dsimp
  simp [evens, odds]
  -- apply?
  apply even_or_odd


example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := rfl
example : (∅ : Set α) = {x | False} := rfl
example : (univ : Set α) = {x | True} := rfl

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

-- Use the theorem ``Prime.eq_two_or_odd``

#check Prime.eq_two_or_odd

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro x
  simp
  sorry

/-
Bounded quantifiers
-/

section

variable (s t : Set ℕ) (P : ℕ → Prop)

example (h : ∀ x ∈ t, P x) : ∀ x ∈ s ∩ t, P x := by
  rintro x ⟨-, xt⟩
  exact h _ xt

end

/-
Indexed unions
-/

section

-- We can use any index type in place of ℕ
variable (A B : ℕ → Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  rw [mem_iUnion, mem_inter_iff, mem_iUnion]
  -- simp; tauto
  --aesop
  constructor
  . rintro ⟨xs, ⟨i, hi⟩⟩
    use i, hi
  . rintro ⟨i, hi, xs⟩
    use xs, i

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

end function_variables
