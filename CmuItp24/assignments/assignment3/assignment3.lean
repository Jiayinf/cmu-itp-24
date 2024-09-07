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
example (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f + g) := by
  sorry

-- You'll have to guess the name of a theorem to prove this one.
@[exercise "1b" 3]
example (c : ℝ) (hf : StrictMono f) (hc : 0 < c) :
    StrictMono (fun x => c * f x) := by
  sorry

-- This is trickier than you might think. Use `by_cases h : a = b` to split
-- on cases whether `a = b`. You can also use `lt_of_le_of_ne`.
@[exercise "1c" 3]
example (hf : StrictMono f) : Monotone f := by
  sorry

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
  sorry

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
  sorry

@[exercise "2b" 3]
theorem mono_fg : Monotone (f ∘ g) := by
  sorry

end

include adj1 in
@[exercise "2c" 3]
theorem increasing_gf : ∀ a, a ≤ g (f a) := by
  sorry

include adj2 in
@[exercise "2d" 3]
theorem decreasing_fg : ∀ b, f (g b) ≤ b := by
  sorry

/-
Unfortunately, for the theorems you just proved, you have to give the
hypotheses as arguments.
-/

#check mono_fg mono_f mono_g
#check mono_gf mono_f mono_g
#check increasing_gf adj1
#check decreasing_fg adj2

include mono_g adj1 adj2 in
@[exercise "2e" 3]
theorem idempotent_gf : ∀ a, g (f (g (f a))) = g (f a) := by
  sorry

include mono_f adj1 adj2 in
@[exercise "2f" 3]
theorem idempotent_fg : ∀ b, f (g (f (g b))) = f (g b) := by
  sorry

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
  sorry

-- hint: `div_lt_iff'` is useful here
@[exercise "3b" 3]
theorem ex_3b (f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hf : ToInfinity f) :
    ToInfinity (fun x => r * f x) := by
  sorry

-- hint: you can use `le_max_left` and `le_max_right`
@[exercise "3c" 4]
theorem ex_3c (f g : ℝ → ℝ) (hf : ToInfinity f) (hg : ToInfinity g) :
    ToInfinity (f + g) := by
  sorry
