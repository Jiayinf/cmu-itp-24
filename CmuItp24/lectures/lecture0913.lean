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
↔       if and only if    `const ructor` `rcases`, `h.1` / `h.2`,
                                         `h.mp` / `h.mpr`, `rw`
∨       or                `left`         `rcases`
                          `right`
False   contradiction                    `contradiction`, `exfalso`
True    this is trivial!  `trivial`


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
  rintro ⟨h1, h2⟩
  constructor
  . apply h2
  . apply h1

example : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  . apply h2
  . apply h1

example : P ∧ Q → Q ∧ P := by
  rintro ⟨h1, h2⟩
  exact ⟨h2, h1⟩

example : P ∧ Q → Q ∧ P :=
  fun ⟨h1, h2⟩ ↦ ⟨h2, h1⟩

example : P ∨ Q → Q ∨ P := by
  rintro (h | h)
  . right; exact h
  . left; exact h

example : (∃ x, R x ∧ S x) → (∃ x, R x) ∧ (∃ x, S x) := by
  intro h
  rcases h with ⟨x, hx⟩
  rcases hx with ⟨hx1, hx2⟩
  sorry

example : (∃ x, R x ∧ S x) → (∃ x, R x) ∧ (∃ x, S x) := by
  intro h
  rcases h with ⟨x, hx1, hx2⟩
  sorry

example : (∃ x, R x ∧ S x) → (∃ x, R x) ∧ (∃ x, S x) := by
  rintro ⟨x, hx1, hx2⟩
  constructor
  . exact ⟨x, hx1⟩
  . exact ⟨x, hx2⟩

example : (∃ x, R x ∧ S x) → (∃ x, R x) ∧ (∃ x, S x) := by
  rintro ⟨x, hx1, hx2⟩
  exact ⟨⟨x, hx1⟩, ⟨x, hx2⟩⟩

example : (∃ x, R x ∧ S x) → (∃ x, R x) ∧ (∃ x, S x) :=
  fun ⟨x, hx1, hx2⟩ ↦ ⟨⟨x, hx1⟩, ⟨x, hx2⟩⟩

example : ∀ z, (∃ x y, R x ∧ S y ∧ y = z) → ∃ x, R x ∧ S z := by
  intro z
  rintro ⟨x, y, hrx, hsy, heq⟩
  rw [←heq]
  use x

example : ∀ z, (∃ x y, R x ∧ S y ∧ y = z) → ∃ x, R x ∧ S z := by
  intro z
  rintro ⟨x, y, hrx, hsy, rfl⟩
  -- use x
  exact ⟨x, hrx, hsy⟩

end

/-
More on negation.
-/

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x h'
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨y, hy⟩
  apply h y hy

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨y, hy⟩
  apply h _ hy

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, hx⟩
  apply hx (h' x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x

/-
More stuff.
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε hε
  use 0
  intro n _
  simpa

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε hε
  dsimp
  have : ε / 2 > 0 := by
    linarith
  specialize cs (ε / 2) this
  specialize ct (ε / 2) this
  rcases cs with ⟨N₀, hN₀⟩
  rcases ct with ⟨N₁, hN₁⟩
  use max N₀ N₁
  intro n hn
  have h₀ : n ≥ N₀ := le_of_max_le_left hn
  have h₁ : n ≥ N₁ := le_of_max_le_right hn
  specialize hN₀ n h₀
  specialize hN₁ n h₁
  sorry
