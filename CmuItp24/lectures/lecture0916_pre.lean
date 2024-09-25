import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 4 is in the repository.

Remember, the first half of the course is focused on weekly exercises;
the second half, after spring break, will be focused on projects.

# Recap

We are just about done with Chapter 3 of Mathematics in Lean.

IOU a proof of the IVT, but I want to start on Chapter 4.

# Agenda

-/

/-
Automation.
-/

section

variable (P Q : Prop)
variable (R S : ℕ → Prop)

example : P ∧ Q → Q ∧ P := by
  sorry

example : P ∨ Q → Q ∨ P := by
  sorry

example : (∃ x, R x ∧ S x) → (∃ x, R x) ∧ (∃ x, S x) := by
  sorry

example : ∀ z, (∃ x y, R x ∧ S y ∧ y = z) → ∃ x, R x ∧ S z := by
  sorry

end


/-
An ε - δ proof.
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  sorry


/-
Set theory.

In set theoretic foundations, everything is a set:

{ 0, 1, 2, Pi, the identity function on ℝ × ℝ, the Eiffel Tower }

In type theory, everything has a fundamental data type, and we
consider sets of elements of a type.
-/

open Set Nat Function

variable {α β γ : Type*} {I : Type*}

section set_variables

variable (x : α)
variable (s t u : Set α)

/-
# Notation
-/

#check s ⊆ t        -- \sub
#check x ∈ s        -- \in or \mem
#check x ∉ s        -- \nin
#check s ∩ t        -- \i or \cap
#check s ∪ t        -- \un or \cup
#check (∅ : Set α)  -- \empty
#check (univ : Set α)

/-
# Examples
-/

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  sorry

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  sorry

-- Type set difference as ``\\``.
-- ``x ∈ s \ t`` expands to ``x ∈ s ∧ x ∉ t``.

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

/-
# Proving two sets are equal
-/

-- the ext tactic

example : s ∩ t = t ∩ s := by
  sorry

/-
# Set-builder notation
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

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
  sorry

example (x : ℕ) : x ∈ (univ : Set ℕ) := by
  sorry

#check Prime.eq_two_or_odd

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬ Even n } := by
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
