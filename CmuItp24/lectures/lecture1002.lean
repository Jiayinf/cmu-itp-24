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
variable (C_def : ∀ n, C n = A n \ ⋃ i < n, A i)

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
  intro h
  -- have := aux h
  -- rcases this with ⟨i, hi, hi'⟩
  rcases aux h with ⟨i, hi, hi'⟩
  simp [C_def]  -- can use simp? to clean up
  use i

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
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  intro x
  -- simp?
  simp only [mem_inter, mem_union, and_imp]
  tauto

example : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  simp; tauto

#eval range 10
#eval Finset.card (range 10)
#eval (range 10).card
#eval (range 10).card.gcd 5

#eval (range 20).filter (fun x => x^2 < 18)
#eval (range 20).filter Even
#eval (range 20).filter Odd
#eval (range 200).filter Nat.Prime

#eval ((range 20).filter Odd).card
#eval (range 20).filter Odd |>.card

end

/-
More induction on the natural numbers.
-/

#check Nat.factorial

def fac : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fac n

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)
open Finset

#check Finset.sum s f
#check Finset.prod s f

#eval Finset.sum (Finset.range 10) (fun n => n^2)
#eval range 10 |>.sum fun n => n^2

open BigOperators

#eval ∑ n ∈ range 10, n^2
#eval ∑ n in range 10, n^2   -- old notation

example : s.sum f = ∑ x ∈ s, f x := rfl
example : s.prod f = ∏ x ∈ s, f x := rfl

example : (range n).sum f = ∑ x ∈ range n, f x := rfl
example : (range n).prod f = ∏ x ∈ range n, f x := rfl

example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 := by
  -- rw [sum_range_zero]
  rfl

example (f : ℕ → ℕ) (n : ℕ): ∑ x ∈ range n.succ, f x = (∑ x ∈ range n, f x) + f n := by
  -- rw?
  rw [sum_range_succ]
  -- rfl doesn't work

example (f : ℕ → ℕ) : ∏ x ∈ range 0, f x = 1 :=
  rfl

example (f : ℕ → ℕ) (n : ℕ): ∏ x ∈ range n.succ, f x = (∏ x ∈ range n, f x) * f n := by
  rw [prod_range_succ]

example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  induction' n with n ih
  . rfl
    -- simp [fac]
  rw [fac, prod_range_succ, ih, mul_comm]
  --simp [fac, ih, mul_comm]

theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  -- apply?
  apply Nat.eq_div_of_mul_eq_right
  . simp -- norm_num
  induction' n with n ih
  . rfl
  rw [sum_range_succ, mul_add, ih]
  ring

-- same proof!

theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 := by
  apply Nat.eq_div_of_mul_eq_right
  . simp
  induction' n with n ih
  . rfl
  rw [sum_range_succ, mul_add, ih]
  ring

end
