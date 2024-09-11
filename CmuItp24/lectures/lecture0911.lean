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
  exfalso
  apply hnQ
  apply hQ

example (hQ : Q) (hnQ : ¬ Q) : ∀ x, P x := by
  contradiction

example (hQ : 2 + 2 = 5) : ∀ x, P x := by
  contradiction

example (x : ℝ) (hQ : 2 < x) (hnQ : x ≤ 2) : ∀ x, P x := by
  linarith

example (h : Q → R) : ¬ R → ¬ Q := by
  intro h1 h2
  apply h1
  apply h
  exact h2

example (h : Q → R) : ¬ R → ¬ Q := by
show_term {
  intro h1 h2
  exact h1 (h h2) }

example (h : Q → R) : ¬ R → ¬ Q :=
  fun h1 h2 => h1 (h h2)

example (h : ¬ R → ¬ Q) : Q → R := by
  intro h1
  by_contra h2
  have h3 : ¬ Q := by
    exact h h2
  contradiction

example (h : ¬ R → ¬ Q) : Q → R := by
  intro h1
  by_contra h2
  have := h h2
  contradiction

example (h : ¬ R → ¬ Q) : Q → R := by
  intro h1
  contrapose h1
  exact h h1

example (h : Q → R) : ¬ R → ¬ Q := by
  intro h1
  contrapose! h1
  apply h
  apply h1

example (h : Q → R) : ¬ R → ¬ Q := by
  tauto

end

/-
Conjunction
-/

section

variable {x y : ℝ}

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  . assumption
  · linarith

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  . assumption
  · intro h3
    apply h₁
    rw [h3]

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  . assumption
  · intro h3
    apply h₁
    apply le_of_eq
    apply h3.symm
    --rw [h3]
    --symm
    --apply h3

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  . assumption
  · intro h3
    exact h₁ (le_of_eq h3.symm)

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  rcases h with ⟨h1, h2⟩
  contrapose! h2
  exact le_antisymm h1 h2
  -- linarith

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  have h1 := h.left
  have h2 := h.right
  intro h3
  apply h2
  exact le_antisymm h1 h3

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
show_term {
  intro h3
  apply h.right
  exact le_antisymm h.left h3
}

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
  fun h3 => h.right (le_antisymm h.left h3)

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
  -- apply?
  intro h
  have h1 := le_or_gt 0 y
  rcases h1 with h2 | h2
  . rw [abs_of_nonneg h2] at h
    left
    apply h
  . rw [abs_of_neg h2] at h
    right
    apply h

example : x < abs y → x < y ∨ x < -y := by
  intro h
  have h1 := le_or_gt 0 y
  rcases h1 with h2 | h2
  . left; rwa [abs_of_nonneg h2] at h
  . right; rwa [abs_of_neg h2] at h

end
