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
- should be an up to date version of VS Code
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
  sorry

end

-- notice that applying `h1` to arguments is like function application
section
variable (f : ℕ → ℕ) (x : ℕ)

#check f x

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
  have h1 : y * z = y * (y * z) * (y * z) * z
  · sorry
  have h2 : z * y = y * (y * z) * (y * z) * z
  · sorry
  sorry

#check mul_left_cancel

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z * (y * z) = y * z * (z * y)
  · sorry
  exact mul_left_cancel h1

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
  sorry


example (ha : a1 ≡ a2 [ZMOD n]) (k : ℕ) : a1^k ≡ a2^k [ZMOD n] := by
  sorry

end

/-
Calculation blocks
-/

example (a b c d e : ℕ) (h1 : a = b + 1)
    (h2 : d = c + a) (h3 : e = b + c) :
    d = e + 1 := by
  calc d
    = c + a := by sorry
  _ = c + (b + 1) := by sorry
  _ = e + 1 := by sorry


/-
A *group* is a structure with *, ⁻¹, 1 satisfing the basic group laws.

  https://en.wikipedia.org/wiki/Group_(mathematics)

Lean lets us declare a group as follows.
-/

section

variable {G : Type*} [Group G]

#check inv_mul_cancel
#check mul_one
#check one_mul
#check mul_assoc

example (a b : G) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_inv_cancel, mul_one]

example {a b c : G} (h : a * b = a * c) : b = c :=
calc b
    = a⁻¹ * (a * b) := by rw [←mul_assoc, inv_mul_cancel, one_mul]
  _ = a⁻¹ * (a * c) := by rw [h]
  _ = c             := by rw [←mul_assoc, inv_mul_cancel, one_mul]

#check mul_left_cancel
