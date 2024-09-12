import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 3 is in the repository, due midnight on Friday.

For exercise 1d:

- Use trichotomy to find a good case split.
- Each case is then easy.


# Recap

We started Chapter 3 of Mathematics in Lean.

→       \to, \r       if ... then         implication
∀       \all          for all             universal quantifier
∃       \ex           there exists        existential quantifier
¬       \not, \n      not                 negation
∧       \and          and                 conjunction
↔       \iff, \lr     if and only if      bi-implication
∨       \or           or                  disjunction
False                 contradiction       falsity
True                  this is trivial!    truth

We have looked at ∀, ∃, and ¬ (more coming).

# Agenda

And (∧), Or (∨)

-/

/-
More on negation.
-/

section
variable (P : ℕ → Prop)  (Q R : Prop)

example (hQ : Q) (hnQ : ¬ Q) : ∀ x, P x := by
  sorry

example (hQ : Q) (hnQ : ¬ Q) : ∀ x, P x := by
  sorry

example (hQ : 2 + 2 = 5) : ∀ x, P x := by
  sorry

example (x : ℝ) (hQ : 2 < x) (hnQ : x ≤ 2) : ∀ x, P x := by
  sorry

example (h : Q → R) : ¬ R → ¬ Q := by
  sorry

example (h : ¬ R → ¬ Q) : Q → R := by
  sorry

end

/-
Conjunction
-/

section

variable {x y : ℝ}

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  sorry

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  sorry

end


/-
Disjunction
-/

section

variable (x y : ℝ)

#check le_or_gt 0 y
#check abs_of_nonneg
#check abs_of_neg

example : x < abs y → x < y ∨ x < -y := by
  sorry

end

/-
More examples, using `rcases`, `rintros`, anonymous constructors, and
pattern matching.
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
More on negation.
-/

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

/-
More stuff.
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  sorry

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  sorry

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  sorry

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  sorry

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  sorry

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  sorry

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  sorry
