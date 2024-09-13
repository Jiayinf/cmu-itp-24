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
  sorry

@[exercise "1b" 4]
theorem ex1b : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  sorry

@[exercise "1c" 4]
theorem ex1c : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  sorry

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
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
sorry

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
  ApproachesAt (fun x => f x + c) (b + c) a :=
sorry

@[exercise "3b" 4]
theorem approachesAt_comp {f g : ℝ → ℝ} {a b c : ℝ}
  (hf : ApproachesAt f b a) (hg : ApproachesAt g c b) :
    ApproachesAt (g ∘ f) c a :=
sorry

def Continuous (f : ℝ → ℝ) := ∀ x, ApproachesAt f (f x) x

@[exercise "3c" 4]
theorem continuous_add_right {f : ℝ → ℝ} (ctsf : Continuous f) (r : ℝ) :
  Continuous (fun x => f x + r) :=
sorry

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
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : Continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
sorry

-- Use `ivt` to prove this.

@[exercise "4" 8]
theorem ivt' {f : ℝ → ℝ} {a b c : ℝ} (aleb : a ≤ b)
    (ctsf : Continuous f) (hfa : f a < c) (hfb : c < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c := by
  let g := fun x => f x - c
  have : ∃ x, a ≤ x ∧ x ≤ b ∧ g x = 0 := by
    sorry
  dsimp [g] at this
  sorry
