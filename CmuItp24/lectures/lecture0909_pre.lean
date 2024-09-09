import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 3 is in the repository, due midnight on Friday.

Assignment 2 seems to have gone well.
- we will post grades soon, >= autograder score
- partial credit only for substantial progress
- be careful with generative AI
  - answers are often nonsense
  - use it to learn, not to do your homework

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

# Agenda

Finding theorems.

Moving on to the logical connectives.

-/

/-
Finding theorems in the library:

o Try to guess the name and use tab completion.

  https://leanprover-community.github.io/contribute/naming.html

o You can use the API documentation on the mathlib web pages.

  https://leanprover-community.github.io/mathlib_docs/

o You can browse mathlib on Github.

o Use `exact?`, `apply?`, `rw?`, `simp?`

o Use `loogle` in VS Code.

o Use moogle: https://www.moogle.ai/

o Use LeanSearch: https://leansearch.net/

-/

example (a : ℝ) : 0 ≤ a^2 := by
  exact sq_nonneg a

open Real

example (a b c : ℝ) (h : a ≤ b) : c - exp b ≤ c - exp a := by
  rw [sub_le_sub_iff_left, exp_le_exp]
  exact h

/-
Universal and existential quantifers

Forall:
- `intro`
- `apply`, `specialize`

Exists:
- `use`
- `rcases h with ⟨u, hu⟩` with `h : ∃ x, P x` to get `u`, `hu : P u`.
-/

def FnUb (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

def FnHasUb (f : ℝ → ℝ) := ∃ a, FnUb f a

section

variable {f g : ℝ → ℝ} {a b : ℝ}

theorem fnUb_add (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (f + g) (a + b) := by
  sorry

example (ubf : FnHasUb f) (ubg : FnHasUb g) :
    FnHasUb (f + g) := by
  sorry

/-
Negation

- Given a goal `¬ P`, `intro h` gives `h : P` and goal `⊥`.
- Given `h : ¬ P` and goal `⊥`, apply `h` gives goal `P`.
-/

example (h : ∀ a, ∃ x, f x > a) : ¬ FnHasUb f := by
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
