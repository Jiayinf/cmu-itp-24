import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 3 is in the repository, due midnight tonight.

For exercise 1d:

- Use trichotomy to find a good case split.
- Each case is then easy.

Feeback from the TAs:

- We will talk about `simp` and `simp only` soon. They will let you avoid repetitive rewrites.
- It's important to use `·` to structure proofs!
- `calc` is useful; we'll see examples.

# Recap

We are working through Chapter 3 of Mathematics in Lean.

Summary:

→       if ... then       `intro`       `apply`, `have h₃ := h₁ h₂`
∀       for all           `intro`       `apply`, `specialize`,
                                        `have h₂ := h₁ t`
∃       there exists      `use`         `rcases`
¬       not               `intro`       `apply`, `contradiction`
∧       and               `constructor` `rcases`, `h.1` / `h.2`,
                                        `h.left` / `h.right`
↔       if and only if    `split`        `rcases`, `h.1` / `h.2`,
                                         `h.mp` / `h.mpr`, `rw`
∨       or                `left`         `rcases`
                          `right`
false   contradiction                    `contradiction`, `exfalso`
true    this is trivial!  `trivial`


# Agenda

More practice, and examples: convergence proofs.

-/

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
