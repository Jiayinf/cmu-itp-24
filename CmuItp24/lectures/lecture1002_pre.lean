import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 5 is graded. It was a bit harder. I'll go over 4b.

Assignment 6 is online.

# Agenda

- exercise 4b from assignment 5.
- finsets (briefly).
- sums and products.
- more about induction on the natural numbers.
- more about structural induction.
-/

namespace set_sequences

variable {α : Type*}
variable (A C : ℕ → Set α)
variable (C_def : ∀ n, C n = A n \ (⋃ i < n, A i))

section
open Classical

lemma aux {A : ℕ → Set α} {x : α} (h : ∃ i, x ∈ A i) :
    ∃ i, x ∈ A i ∧ ∀ j < i, x ∉ A j :=
  Subtype.existsOfSubtype (Nat.findX h)

include C_def

theorem Union_C_eq_Union_A : (⋃ i, C i) = (⋃ i, A i) := by
  ext x
  simp
  constructor
  · rintro ⟨n, xmem⟩
    rw [C_def n] at xmem
    simp at xmem
    use n, xmem.1
  sorry

end

end set_sequences

/-
Finsets.
-/

#eval ({1, 2, 3} : Finset ℕ)
#eval ({1, 2, 3} ∩ {2, 3, 4} : Finset ℕ)
#eval ({1, 2, 3} ∪ {2, 3, 4} : Finset ℕ)

section
variable (s t u : Finset ℕ)

open Finset

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  sorry

example : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  sorry

end

/-
More induction on the natural numbers.
-/

def fac : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fac n

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

#eval Finset.sum (Finset.range 10) (fun n => n^2)

open BigOperators
open Finset

#eval Finset.sum (Finset.range 10) (fun n => n^2)

#eval ∑ n ∈ range 10, n^2

example : s.sum f = ∑ x ∈ s, f x := rfl
example : s.prod f = ∏ x ∈ s, f x := rfl

example : (range n).sum f = ∑ x ∈ range n, f x := rfl
example : (range n).prod f = ∏ x ∈ range n, f x := rfl

example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 := by
  sorry

example (f : ℕ → ℕ) (n : ℕ): ∑ x ∈ range n.succ, f x = (∑ x ∈ range n, f x) + f n := by
  sorry

example (f : ℕ → ℕ) : ∏ x ∈ range 0, f x = 1 :=
  sorry

example (f : ℕ → ℕ) (n : ℕ): ∏ x ∈ range n.succ, f x = (∏ x ∈ range n, f x) * f n := by
  sorry

example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  sorry

theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  sorry

theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 := by
  sorry

end

/-
Another style of writing proofs by structural induction.
-/

section

variable {α β γ : Type*}
variable (as bs cs : List α)
variable (a b c : α)

open List

theorem append_nil' : as ++ [] = as := by
  induction' as with a as ih
  . rfl
  . rw [cons_append, ih]

-- do the lightbulb trick!

/-
Another example:
-/

#eval map (fun n => n^2) [1, 2, 3, 4, 5]

-- We write the argument that doesn't vary in recursive calls on the left-hand side of `:` (the colon).
def map' (f : α → β) : List α → List β
  | []      => []
  | a :: as => f a :: map' f as

#eval map' (fun n => n^2) [1, 2, 3, 4, 5]

theorem map'_map' (f : α → β) (g : β → γ) (as : List α) :
    map' g (map' f as) = map' (g ∘ f) as := by
  induction' as with a as ih
  . rfl
  .  simp [map', ih]

-- do it again!

/-
Reversing a list.
-/

def bad_reverse : List α → List α
  | []      => []
  | a :: as => concat (bad_reverse as) a

/-- `reverse_aux as acc` reverses `as` and appends `acc` -/
def reverse_aux : List α → List α → List α
  | [],      acc => acc
  | a :: as, acc => reverse_aux as (a :: acc)

def reverse' (as : List α) := reverse_aux as []

theorem reverse_aux_append (as bs cs : List α) :
    reverse_aux (as ++ bs) cs = reverse_aux bs (reverse_aux as cs) := by
  sorry

theorem reverse_aux_append' (as bs cs : List α) :
    reverse_aux as (bs ++ cs) = (reverse_aux as bs) ++ cs := by
  sorry

theorem reverse'_append (as bs : List α) :
    reverse' (as ++ bs) = reverse' bs ++ reverse' as := by
  sorry

end
