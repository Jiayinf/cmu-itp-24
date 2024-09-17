import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 4 is in the repository.

Remember, the first half of the course is focused on weekly exercises;
the second half, after fall break, will be focused on projects.

# Recap

We are just about done with Chapter 3 of Mathematics in Lean.

IOU a proof of the IVT, but I want to start on Chapter 4.

# Agenda

- automation for propositional logic
- convergence and `calc`
- `Set`s in Lean

-/

/-
Automation.
-/

section

variable (P Q : Prop)
variable (R S : ℕ → Prop)

example : P ∧ Q → Q ∧ P := by
  tauto

example : P ∨ Q → Q ∨ P := by
  tauto

example : (∃ x, R x ∧ S x) → (∃ x, R x) ∧ (∃ x, S x) := by
  tauto

example : ∀ z, (∃ x y, R x ∧ S y ∧ y = z) → ∃ x, R x ∧ S z := by
  aesop

end


/-
An ε - δ proof.
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (s + t) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  specialize hs n ngeNs
  specialize ht n ngeNt
  calc abs (s n + t n - (a + b))
      = abs ((s n - a) + (t n - b)) := by
        congr; abel
    _ ≤ abs (s n - a) + abs (t n - b) := by
        apply abs_add_le
    _ < ε / 2 + ε / 2 := by
        -- linarith
        apply add_lt_add hs ht
    _ = ε := by simp

/-
Set theory.

In set-theoretic foundations, everything is a set:

{ 0, 1, 2, Pi, the identity function on ℝ × ℝ, the Eiffel Tower }

In type theory, everything has a fundamental data type, and we
consider sets of elements of a type.
-/

#check Set ℕ
#check Set (ℕ × ℕ)
#check Set (ℕ → ℝ)

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
#check ∅
#check (∅ : Set α)  -- \empty
#check (univ : Set α)

/-
# Examples
-/

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  simp only [mem_setOf]
  rw [subset_def] at h
  rintro x ⟨xs, xt⟩
  constructor
  . apply h x xs
  . exact xt

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs, xt⟩
  exact ⟨h xs, xt⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  rintro x ⟨xs, (xt | xu)⟩
  . left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  intro x; simp; tauto

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  intro x; aesop

-- Type set difference as ``\\``.
-- ``x ∈ s \ t`` expands to ``x ∈ s ∧ x ∉ t``.

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

/-
# Proving two sets are equal
-/

example : s ∩ t = t ∩ s := by
  -- apply subset_antisymm
  ext x
  constructor
  . rintro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  . simp; tauto

example : s ∩ t = t ∩ s := by
  ext x; simp; tauto

example : s ∩ t = t ∩ s := by
  -- apply?
  exact inter_comm s t
