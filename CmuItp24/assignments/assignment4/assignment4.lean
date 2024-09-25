import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import CmuItp24.Autograde

namespace assignment4

/-
EXERCISE 1.

Prove the following without using automation, i.e. only with basic tactics
such as `intros`, `apply`, `split`, `cases`, `left`, `right`, and `use`.
-/

section

variable {α β : Type} (P Q : α → Prop) (R : α → β → Prop)

@[exercise "1a" 4]
theorem ex1a : (∀ x, P x) ∧ (∀ x, Q x) → ∀ x, P x ∧ Q x := by
  intros h x
  exact ⟨h.left x, h.right x⟩

@[exercise "1b" 4]
theorem ex1b : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  intros h x
  cases h
  case inl hP =>
    left
    exact hP x
  case inr hQ =>
    right
    exact hQ x

@[exercise "1c" 4]
theorem ex1c : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  intros h y  
  rcases h with ⟨x, hx⟩
  use x
  exact hx y

end


/-
EXERCISE 2.

Suppose two pairs of real numbers {a, b} and {c, d} have the same sum
and product. The following theorem shows that either a = c and b = d,
or a = d and b = c. Fill in the details. You can use `ring` and `linarith`
freely.

Hint: consider `(a - c) * (a - d)`. You will have to find theorems in the
library, using the techniques we discussed in class.
-/

@[exercise "2" 8]
theorem sum_product_magic (a b c d : ℝ)
    (sumeq : a + b = c + d) (prodeq : a * b = c * d) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  -- consider polynomial `(x - a)(x - b) = (x - c)(x - d)` in terms of roots
  have h : (λ x : ℝ => (x - a) * (x - b)) = (λ x : ℝ => (x - c) * (x - d)) := by

    funext x
    calc
      (x - a) * (x - b) = x^2 - (a + b) * x + a * b := by ring
      _ = x^2 - (c + d) * x + c * d := by rw [sumeq, prodeq]
      _ = (x - c) * (x - d) := by ring


  by_cases h1 : a = c
  · left
    exact ⟨h1, by linarith [sumeq, prodeq, h1]⟩

  · right
    have h2 : b = c + d - a := by
      linarith [sumeq]


    have h_3 : a * (c + d - a) = c * d := by
      rw [h2] at prodeq
      exact prodeq
    have h3 : a * c + a * d - a * a = c * d := by
      rw [← h_3]
      ring


    have h4 : (a - d) * (a - c) = 0 := by
      linarith [h3]


    have h5 : (a - d) * (a - c) = 0 := by
      linarith [h4]


    have h6 : a = d := by

      have h_ne_c : a - c ≠ 0 := by
        intro h_eq
        apply h1
        linarith

      have h_eq_zero : a - d = 0 := by

        have h_mul_zero : (a - d) * (a - c) = 0 := h5

        apply (mul_eq_zero.mp h_mul_zero).resolve_right h_ne_c


      exact eq_of_sub_eq_zero h_eq_zero


    have h7 : b = c := by
      rw [h6] at sumeq
      linarith [sumeq]

    exact ⟨h6, h7⟩
/-
EXERCISE 3.

The predicate `ApproachesAt f b a` should be read "f(x) approaches b as x
approaches a", and the predicate `Continuous f` says that f is continuous.

Prove the following two theorems.

Note that bounded quantification such as `∀ ε > 0, ..` really means `∀ ε, ε > 0 → ..`
and `∃ δ > 0, ..` really means `∃ δ, δ > 0 ∧ ..`.
-/

def ApproachesAt (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

@[exercise "3a" 4]
theorem approachesAt_add_right  {f : ℝ → ℝ} {a b c: ℝ}
    (hf : ApproachesAt f b a) :
  ApproachesAt (fun x => f x + c) (b + c) a := by
  intros ε hε

  rcases hf ε hε with ⟨δ, hδ_pos, hδ⟩

  use δ, hδ_pos
  intros x hx

  calc
    abs ((f x + c) - (b + c)) = abs (f x - b) := by ring_nf
    _ < ε := hδ x hx

@[exercise "3b" 4]
theorem approachesAt_comp {f g : ℝ → ℝ} {a b c : ℝ}
  (hf : ApproachesAt f b a) (hg : ApproachesAt g c b) :
    ApproachesAt (g ∘ f) c a := by
    intros ε hε
    rcases hg ε hε with ⟨δg, hδg_pos, hδg⟩
    rcases hf δg hδg_pos with ⟨δf, hδf_pos, hδf⟩
    use δf, hδf_pos
    intros x hx
    specialize hδf x hx
    specialize hδg (f x) hδf
    exact hδg

def Continuous (f : ℝ → ℝ) := ∀ x, ApproachesAt f (f x) x

@[exercise "3c" 4]
theorem continuous_add_right {f : ℝ → ℝ} (ctsf : Continuous f) (r : ℝ) :
  Continuous (fun x => f x + r) := by
  intros x
  apply approachesAt_add_right
  exact ctsf x

-- Since `f x - r` is the same as `f x + (- r)`, the following is an instance
-- of the previous theorem.
theorem continuous_sub {f : ℝ → ℝ} (ctsf : Continuous f) (r : ℝ) :
  Continuous (fun x => f x - r) :=
continuous_add_right ctsf (-r)

/-
EXERCISE 4.

In class, I will prove the intermediate value theorem in the form `ivt`.
Use that version to prove the more general one that comes after.
-/

-- We'll do this in class! You don't have to prove it.
variable
  (ivt : {f : ℝ → ℝ} → {a b : ℝ} →
    a ≤ b → Continuous f → f a < 0 → 0 < f b →
    ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0)

-- Use `ivt` to prove this.
include ivt

@[exercise "4" 8]
theorem ivt' {f : ℝ → ℝ} {a b c : ℝ} (aleb : a ≤ b)
    (ctsf : Continuous f) (hfa : f a < c) (hfb : c < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c := by

  let g := fun x => f x - c

  have h_g_cont : Continuous g := by
    apply continuous_add_right ctsf (-c)

  have h_ga : g a < 0 := by
    calc
      g a = f a - c := rfl
      _ < 0 := by linarith [hfa]

  have h_gb : g b > 0 := by
    calc
      g b = f b - c := rfl
      _ > 0 := by linarith [hfb]

  have : ∃ x, a ≤ x ∧ x ≤ b ∧ g x = 0 := by
    apply ivt aleb
    exact h_g_cont
    exact h_ga
    exact h_gb

  dsimp [g] at this
  rcases this with ⟨x, h1, h2, h3⟩
  use x
  exact ⟨h1, h2, by linarith⟩
