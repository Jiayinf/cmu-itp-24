import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignmnent 2 is in the repository `github.com/hoskinson-center/cmu-itp-24`.
(The old address still works.)

Correction to the assignment: "four identities" -> "five identities"

Do the following:

- Pull the repository.
- Copy `assignments/assignment2.lean` to `assignments/solutions2.lean`.
- Fill in the sorry's with proofs as best you can.
- Upload the result to gradescope.
- You can upload updates as many times as you want.

This assignment is due midnight.

Q: When should future assignments be due?

Notes:

- If you get a message that says "Imports are out of date and must be rebuilt;
use the "Restart File" command in your editor," press the blue "Restart File" button
in the lower right corner of the Infoview Window, use ctrl-shift-P and type
"Lean 4: Server: Restart File." You should see the yellow bars for a few seconds.
If they stick around much longer, something has gone wrong!

Revised office hours:

- Wednesday, 11–12 (Wojciech)
- Wednesday, 1–2 (Jeremy)
- Wednesday, 3:30–4:30 (Eric)
- Thursday, 11–12 (Wojciech)
- Thursday, 4–5 (Eric)
- Friday, 10–11 (Jeremy)

Office hours are all in Baker Hall 139, the Hoskinson Center.

# Recap

We have been working through Chapter 2 of Mathematics in Lean.

You have seen: `rw`, `apply`, `have`, `calc`

# Agenda

Goal: finish up Chapter 2 of MIL.

- automation: `ring` and `abel`
- algebraic structures

-/

/-
Groups where every element has order 2.
-/

section

variable {G : Type*} [Group G]

#check inv_mul_cancel
#check mul_one
#check one_mul
#check mul_assoc

-- from last time
example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z = y * (y * z) * (y * z) * z := by
    rw [mul_assoc y, h, mul_one]
  have h2 : z * y = y * (y * z) * (y * z) * z := by
    rw [← mul_assoc y, h, one_mul, mul_assoc, mul_assoc, h, mul_one]
  rw [h1, h2]

#check mul_left_cancel

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z * (y * z) = y * z * (z * y) := by
    rw [h, ←mul_assoc, mul_assoc y, h, mul_one, h]
  exact mul_left_cancel h1

example (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

example {a b c : G} (h : a * b = a * c) : b = c := by
  have h1 : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by
    rw [h]
  rw [←mul_assoc, ←mul_assoc, inv_mul_cancel, one_mul, one_mul] at h1
  exact h1

example {a b c : G} (h : a * b = a * c) : b = c := by
  have h1 : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by
    rw [h]
  rwa [←mul_assoc, ←mul_assoc, inv_mul_cancel, one_mul, one_mul] at h1

/-
Ring and abel.
-/

example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 := by ring

example (a b : ℝ) : (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := by ring

example (a b c : ℝ) : c + a + b + a - c = 2 * a + b := by ring

example : 65 * 3 = 195 := by norm_num

section

variable (R : Type) [CommRing R]

example (a b : R) : (a + b) * (a - b) = a^2 - b^2 := by ring

example (a b : R) : (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := by ring

example (a b c : R) : c + a + b + a - c = 2 • a + b := by ring

end

example (A : Type*) [AddCommGroup A] (a b c : A) : c + a + b + a - c = 2 • a + b := by abel

/-
Examples:
-/

#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  exact h₀
  exact h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  exact h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  exact le_trans h₀ h₁


section
variable (a b c d e : ℝ)

#check lt_of_le_of_lt

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
    a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
    a < e := by
  linarith

end

/-
From assignment 2
-/

section
variable (x y z : ℝ)

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
  abs (x + y + z) ≤ 19 := by
  trans 10 + 5 + 4
  apply le_trans
  apply abs_add
  apply add_le_add
  apply le_trans
  apply abs_add
  apply add_le_add hx hy
  exact hz
  norm_num
