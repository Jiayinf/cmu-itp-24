import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Recap from last time

By now, you should:
- see this course on Piazza and Gradescope
- have Lean installed
- have Mathlib installed
- have fetched the course repository

Any problems, let us know!
- should be an up-to-date version of VS Code
- don't forget to enter your ssh key on Github
- what's up with the ∀?

Last time, we started with `rewrite` in MIL.

# Announcements

Revised office hours:

- Wednesday, 11–12 (Wojciech)
- Wednesday, 1–2 (Jeremy)
- Wednesday, 3:30–4:30 (Eric)
- Thursday, 11–12 (Wojciech)
- Thursday, 4–5 (Eric)
- Friday, 10–11 (Jeremy)

Office hours are all in Baker Hall 139, the Hoskinson Center.

Assignment 2 is now in the course repository.

Copy `assignment2.lean` to `solutions2.lean` to work on it.

# Agenda

Today, we will continue working through `MIL`, with `apply` and `rw`.

-/

/-
The `apply` tactic.
-/

section
variable (P Q R : ℕ → Prop)

theorem foo1 (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  apply h2
  apply h1
  apply h3

example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  apply h2
  apply h1
  exact h3

example (a : ℕ) (h1 : ∀ x, P x → Q x)
    (h2 : ∀ x, Q x → R x)
    (h3 : P a) :
    R a := by
  apply h2
  apply h1
  assumption

end

-- notice that applying `h1` to arguments is like function application
section
variable (f : ℕ → ℕ) (x : ℕ)

#check f x

variable (P Q : Prop) (h : P → Q) (h1 : P)

#check h h1

end

/-
Groups where every element has order 2.
-/

section

variable {G : Type*} [Group G]

#check inv_mul_cancel
#check mul_one
#check one_mul
#check mul_assoc

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z = y * (y * z) * (y * z) * z := by
    rw [mul_assoc y, h, mul_one]
  have h2 : z * y = y * (y * z) * (y * z) * z := by
    rw [← mul_assoc y, h, one_mul, mul_assoc, mul_assoc, h, mul_one]
  rw [h1, h2]

end

/-
Integer ModEq
-/

#check Int.ModEq
#check Int.ModEq.refl
#check Int.ModEq.symm
#check Int.ModEq.trans
#check Int.ModEq.add
#check Int.ModEq.add_left

section

variable (a1 a2 b1 b2 c1 c2 n : ℤ)

example (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD n] := by
  apply Int.ModEq.add
  apply Int.ModEq.mul
  assumption
  assumption
  assumption

example (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD n] := by
  apply Int.ModEq.add
  apply Int.ModEq.mul
  repeat { assumption }

example (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD n] := by
  show_term {
  apply Int.ModEq.add
  · apply Int.ModEq.mul
    assumption
    assumption
  · assumption }

example (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD n] :=
Int.ModEq.add (Int.ModEq.mul ha hb) hc

example (ha : a1 ≡ a2 [ZMOD n]) (k : ℕ) : a1^k ≡ a2^k [ZMOD n] := by
  induction' k with k ih
  . rw [pow_zero, pow_zero]
  . rw [pow_succ, pow_succ]
    exact Int.ModEq.mul ih ha
end

/-
Calculation blocks
-/

example (a b c d e : ℕ) (h1 : a = b + 1)
    (h2 : d = c + a) (h3 : e = b + c) :
    d = e + 1 := by
  calc
  d = c + a       := by rw [h2]
  _ = c + (b + 1) := by rw [h1]
  _ = e + 1       := by rw [h3, add_comm b c, add_assoc]
