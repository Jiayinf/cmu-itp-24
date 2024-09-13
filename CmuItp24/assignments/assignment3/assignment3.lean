import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import CmuItp24.Autograde

/-
FIRST EXERCISE: Strict monotonicity

Section 3.1 of MIL discusses the `monotone` predicate. There is also a strict
version. Prove the theorems below, *and* come up with suitable names
(in other words, replace `example` with `theorem foo`.)

(Don't use any library theorems about `strict_mono` or `monotone`! You should
only use basic properties of orderings.)
-/

#print Monotone
#print StrictMono

namespace strictMono_exercise

variable (f : ℝ → ℝ) (g : ℝ → ℝ)

@[exercise "1a" 3]
theorem strictMonoAdd (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f + g) := by
  intros x1 x2 hlt
  apply add_lt_add
  exact hf hlt
  exact hg hlt

-- You'll have to guess the name of a theorem to prove this one.
@[exercise "1b" 3]
theorem strictMonoMulC (c : ℝ) (hf : StrictMono f) (hc : 0 < c) :
    StrictMono (fun x => c * f x) := by
  intros x1 x2 hlt
  apply mul_lt_mul_of_pos_left
  exact hf hlt
  exact hc

-- This is trickier than you might think. Use `by_cases h : a = b` to split
-- on cases whether `a = b`. You can also use `lt_of_le_of_ne`.
@[exercise "1c" 3]
theorem strictMonoComp (hf : StrictMono f) : Monotone f := by
  intros x1 x2 hle
  by_cases h : x1 = x2
  · rw [h]
  · apply le_of_lt
    apply hf
    exact lt_of_le_of_ne hle h

/-
The following (trivial) example shows how to use trichotomy. You do not need
to fully understand the pattern now; you can take it as a black box.
-/

example (x1 x2 : ℝ) : x1 ≤ x2 ∨ x2 < x1 := by
  rcases lt_trichotomy x1 x2 with h | h | h
  · -- In this case, we have `h : x1 < x2`.
    left
    apply le_of_lt h
  · -- In this case, we have `h : x1 = x2`.
    left
    rw [h]
  -- In this case, we have `h : x2 < x1`
  right
  exact h

open Function

/-
Here is an example that shows that `x ↦ x + 1` is injective.
-/

example : Injective (fun x => x + 1) := by
  intros x1 x2 h
  dsimp at h  -- this makes `h` more readable
  exact add_right_cancel h

/-
Show that every strictly monotone function is injective.
-/

@[exercise "1d" 3]
theorem injective_of_strictMono (hf : StrictMono f) : Injective f := by
  -- intros x1 x2 h
  -- by_cases hlt : x1 < x2
  -- · have h_strict : f x1 < f x2 := hf hlt
  --   rw [h] at h_strict
  --   exact False.elim (lt_irrefl (f x2) h_strict)
  -- · have h_strict : f x2 < f x1 := hf (lt_of_not_lt hlt)
  --   rw [←h] at h_strict
  --   exact False.elim (lt_irrefl (f x1) h_strict)
  intros x1 x2 h
  by_cases hlt : x1 < x2
  · have h_strict : f x1 < f x2 := hf hlt
    rw [h] at h_strict
    exact False.elim (lt_irrefl (f x2) h_strict)
  · by_cases hge: x2 < x1
    · have h_strict : f x2 < f x1 := hf hge
      rw [←h] at h_strict
      exact False.elim (lt_irrefl (f x1) h_strict)
    · exact le_antisymm (le_of_not_lt hge) (le_of_not_lt hlt)

end strictMono_exercise

/-
SECOND EXERCISE: Galois connections

Given `α` with a partial order, a *closure operator* `cl : α → α` has the
following properties:

- `cl` is monotone
- `cl` is increasing, in the sense that for every `a : α`, `a ≤ cl a`
- `cl` is idempotent, in the sense that for every `a : α`, `cl (cl a) = cl a`.

Given `α` and `β` with partial orders, a *Galois connection* is a pair of
monotone functions `f : α → β` and `g : β → α` satisfying the following:

  For every `a` and `b`, `f a ≤ b` if and only if `a ≤ g b`.

You can read more about these here:

  https://en.wikipedia.org/wiki/Closure_operator
  https://en.wikipedia.org/wiki/Galois_connection

The exercises below ask you to show that if `f` and `g` form a Galois
connection, then `g ∘ f` is a closure operator, and `f ∘ g` is a closure
operator on the reverse order.
-/

namespace galois_connection_exercise

variable {α β : Type*}
variable [PartialOrder α] [PartialOrder β]
variable {f : α → β}
variable {g : β → α}
variable (mono_f : Monotone f)
variable (mono_g : Monotone g)
variable (adj1 : ∀ a b, f a ≤ b → a ≤ g b)
variable (adj2 : ∀ a b, a ≤ g b → f a ≤ b)

section
-- you can use these:
include mono_f mono_g

-- If you see linter warnings about an "included section variable" here,
-- ignore them.

@[exercise "2a" 3]
theorem mono_gf : Monotone (g ∘ f) := by
  intros a1 a2 h
  have h_f : f a1 ≤ f a2 := mono_f h
  have h_gf : g (f a1) ≤ g (f a2) := mono_g h_f
  exact h_gf

@[exercise "2b" 3]
theorem mono_fg : Monotone (f ∘ g) := by
  intros a1 a2 h
  have h_g : g a1 ≤ g a2 := mono_g h
  have h_gf : f (g a1) ≤ f (g a2) := mono_f h_g
  exact h_gf

end

include adj1 in
@[exercise "2c" 3]
theorem increasing_gf : ∀ a, a ≤ g (f a) := by
  intro a
  exact adj1 a (f a) (le_refl (f a))

include adj2 in
@[exercise "2d" 3]
theorem decreasing_fg : ∀ b, f (g b) ≤ b := by
  intro b
  exact adj2 (g b) b (le_refl (g b))

/-
Unfortunately, for the theorems you just proved, you have to give the
hypotheses as arguments.
-/

#check mono_fg mono_f mono_g
#check mono_gf mono_f mono_g
#check increasing_gf adj1
#check decreasing_fg adj2
#check adj2

include mono_g adj1 adj2 in
@[exercise "2e" 3]
theorem idempotent_gf : ∀ a, g (f (g (f a))) = g (f a) := by
  intro a

  have h1 : g (f (g (f a))) ≥ g (f a) := by
    apply increasing_gf adj1

  have h2 : g (f (g (f a))) ≤ g (f a) := by
    apply mono_g
    apply decreasing_fg adj2
  exact le_antisymm h2 h1


include mono_f adj1 adj2 in
@[exercise "2f" 3]
theorem idempotent_fg : ∀ b, f (g (f (g b))) = f (g b) := by
  intro b

  have h1 : f (g (f (g b))) ≥ f (g b) := by
    apply mono_f
    apply increasing_gf adj1

  have h2 : f (g (f (g b))) ≤ f (g b) := by
    apply decreasing_fg adj2

  exact le_antisymm h2 h1

end galois_connection_exercise

/-
THIRD EXERCISE: convergence to infinity

Below, `ToInfinity f` expresses that `f x` approaches infinity as
`x` approaches infinity.

The properties below are analogous to properties proved in Sections 3.2
and 3.6 in Mathematics in Lean. They involve the universal and existential
quantifiers (both no other logical connectives).
-/

def ToInfinity (f : ℝ → ℝ) := ∀ b, ∃ x₀, ∀ x, x₀ ≤ x → b < f x

-- hint: you can use `linarith` at the end
@[exercise "3a" 3]
theorem ex_3a (f : ℝ → ℝ) (r : ℝ) (hf : ToInfinity f) :
    ToInfinity (fun x => f x  + r) := by
  intro b
  obtain ⟨x₀, h₀⟩ := hf (b - r)
  use x₀
  intro x hx
  specialize h₀ x hx
  -- have h1 : f x + r > (b - r) + r := add_lt_add_right h₀ r
  -- simp at h1
  -- exact h1
  dsimp
  linarith



-- hint: `div_lt_iff'` is useful here
@[exercise "3b" 3]
theorem ex_3b (f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hf : ToInfinity f) :
    ToInfinity (fun x => r * f x) := by
  intro b

  let b' := b / r

  obtain ⟨x₀, h₀⟩ := hf b'

  use x₀
  intro x hx

  specialize h₀ x hx

  have h1 : r * f x > r * b' := mul_lt_mul_of_pos_left h₀ hr

  have h2 : b = r * b' :=
    by simp [b', mul_div_cancel₀ b hr.ne']

  exact lt_of_le_of_lt (le_of_eq h2) h1

-- hint: you can use `le_max_left` and `le_max_right`

#check le_max_left

example (f g : ℝ → ℝ) (x : ℝ) : f x + g x = (f + g) x := by
  -- Use `funext` to apply the definition of function addition
  rfl

@[exercise "3c" 4]
theorem ex_3c (f g : ℝ → ℝ) (hf : ToInfinity f) (hg : ToInfinity g) :
    ToInfinity (f + g) := by

  intro b
  obtain ⟨xf, hxf⟩ := hf b
  obtain ⟨xg, hxg⟩ := hg 0

  let x₀ := max xf xg
  use x₀
  intro x hx

  have hx_f : xf ≤ x := le_trans (le_max_left xf xg) hx
  have hx_g : xg ≤ x := le_trans (le_max_right xf xg) hx

  specialize hxf x hx_f
  specialize hxg x hx_g

  have h_sum : b + 0 < f x + g x := add_lt_add hxf hxg

  simp at h_sum

  exact h_sum
