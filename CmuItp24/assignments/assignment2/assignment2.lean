import Mathlib.Analysis.InnerProductSpace.PiL2
import CmuItp24.Autograde

/-
FIRST EXERCISE: the parallelogram law
-/

namespace parallelogram_exercise
open RealInnerProductSpace

/-
In the following variable declaration, `EuclideanSpace ℝ (Fin 2)` represents
the Euclidean plane, ℝ × ℝ, with the usual definition of inner product.
-/

variable (x y z : EuclideanSpace ℝ (Fin 2))

#check ⟪x, y⟫    -- the inner product
#check ‖x‖       -- the norm
#check x + y
#check 3 • x

/-
Hovering over the brackets in VS Code shows that the angle brackets for the inner product can be
written as `\<<` and `\>>`, and the bars for the norm can be written `\||`.

They satisfy the following identities:
-/

example : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := inner_add_right x y z
example : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := inner_add_left x y z
example : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := inner_sub_right x y z
example : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := inner_sub_left x y z

example :  ⟪x, x⟫ = ‖x‖^2 := real_inner_self_eq_norm_sq x

/-
The following identity is known as the *parallelogram law*. It says that the sum of the squares
of the lengths of the four sides of a parallegram is equal to the sum of the squares of the
lengths of the diagonals.

You can read a proof of it on Wikipedia: https://en.wikipedia.org/wiki/Parallelogram_law.

Formalize it using only the five identities above as well as the `ring` tactic.
-/

@[exercise "1a" 8]
theorem paralellogram_law : ‖x + y‖^2 + ‖x - y‖^2  = 2 * (‖x‖^2 + ‖y‖^2) := by
  sorry

/-
In fact, the theorem holds for arbitrary inner product spaces, with exactly the same proof.
You can check this by replacing the variable declaration above by the following:

variables {E : Type*} [inner_product_space ℝ E]
variables x y z : E
-/

end parallelogram_exercise

/-
SECOND EXERCISE: Boolean rings
-/

namespace boolean_ring_exercise

/-
The notion of a ring is discussed in the textbook:
https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#proving-identities-in-algebraic-structures

A *Boolean* ring satisfies the additional property that for every `x`, `x^2 = x`.
You can read about Boolean rings here:
https://en.wikipedia.org/wiki/Boolean_ring
-/

variable {R : Type*} [Ring R]

-- This is the assumption that makes `R` a Boolean ring:
variable (idem : ∀ x : R, x^2 = x)

-- This adds `idem` as a hypothesis to every theorem:
include idem

/-
This exercise asks you to prove that every Boolean ring is commutative, i.e.
satisfies `x * y = y * x` for every `x` and `y`. Unfortunately, we cannot use the
`ring` tactic along the way, since it only works once we know a ring is commutative.
So you will have to rely on theorems like `mul_add`, `add_mul`, etc. in the textbook.
-/

-- This is useful:
theorem mul_idem (x : R) : x * x = x := by
  rw [←pow_two, idem]

-- Unfortunately, you have to write `mul_idem idem` to use it.
example (x y : R) : (x + y) * (x + y) = x + y := by
  rw [mul_idem idem]

/-
Prove the following theorem, following the calculation in Wikipedia:
x + x = (x+x)^2 = x^2 + x^2 + x^2 + x^2 = (x + x) + (x + x).
-/

@[exercise "2a" 6]
theorem add_self (x : R) : x + x = 0 := by
  have h1 : x + x = (x + x) + (x + x) := by
    calc
      x + x = (x + x)^2 := by
        sorry
      _ = x + x + (x + x) := by
        sorry
  have h2 : (x + x) + (x + x) - (x + x) = (x + x) - (x + x) := by
    rw [←h1]
  rw [add_sub_cancel_left, sub_self] at h2
  exact h2


-- Note: again, to use this theorem you have to mention `idem` explicitly
example (y : R) : y + y = 0 :=
add_self idem y

/-
Prove `neg_eq_self` using the calculation `-x = 0 - x = x + x - x = x`. You can use the theorems
`zero_sub` and `add_sub_cancel_right`, as well as `add_self idem`.
-/

@[exercise "2b" 7]
theorem neg_eq_self (x : R) : -x = x := by
  sorry

/-
This is a corollary.
-/

theorem sub_eq_add (x y : R) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_self idem]

/-
Prove this, using the calculation `x = x + y - y = 0 - y = -y = y`.
-/

@[exercise "2c" 6]
theorem eq_of_add_eq_zero {x y : R} (h : x + y = 0) : x = y := by
  sorry

/- Finally, prove `mul_comm` using the following argument from Wikipedia:

`0 + x + y = x + y = (x + y)^2 = x^2 + xy + yx + y^2 = xy + yx + x + y`

You can use the `abel` tactic to rearrange sums.
-/

example (x y : R) : x + x * y + y * x + y = x * y + y * x + x + y := by
  abel

@[exercise "2d" 7]
theorem mul_comm (x y : R) : x * y = y * x := by
  have h1 : 0 + (x + y) = (x * y + y * x) + (x + y) := by
    calc
      0 + (x + y) = (x + y)^2 := by
        sorry
      _ = x * y + y * x + (x + y) := by
        sorry
  have h2 : 0 = x * y + y * x := by
    exact add_right_cancel h1
  show x * y = y * x
  exact eq_of_add_eq_zero idem h2.symm

end boolean_ring_exercise

/-
THIRD EXERCISE: absolute values
-/

namespace absolute_value_exercise

variable (x y z w : ℝ)

/-
Bounding sums often boils down to using transitivity and inequalities. Step through the
next example and make sure you understand what is going on. `swap` switches the order of the goals,
and `norm_num` does a numeric calculation.

The `transitivity` tactic lets you state the intermediate expression. In contrast, applying
`le_trans` lets you make Lean figure it out from context. With the `transitivity` tactic,
we have to specify that the numerals are real numbers, because otherwise Lean assumes that they
are natural numbers.
-/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
    abs (x + y + z) ≤ 19 := by
  transitivity ((10 : ℝ) + 5 + 4)
  swap
  · norm_num
  apply le_trans
  apply abs_add
  apply add_le_add
  · -- first goal
    apply le_trans
    apply abs_add
    exact add_le_add hx hy
  -- second goal
  exact hz

/-
We can finish the second goal earlier by giving `hz` right away.
-/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
    abs (x + y + z) ≤ 19 := by
  transitivity ((10 : ℝ) + 5 + 4)
  swap
  · norm_num
  apply le_trans
  apply abs_add
  -- the underscore means: figure it out or leave it as another goal
  apply add_le_add _ hz
  apply le_trans
  apply abs_add
  exact add_le_add hx hy

/-
Prove the following. You can also use the theorems `abs_sub`, `pow_two` to expand `w^2` to `w * w`,
`sq_abs`, and `mul_le_mul`. For the last theorem, you'll need to know that an absolute value is
nonnegative, which is the theorem `abs_nonneg`. You can also use `norm_num` to show that
`(9 : ℝ) = 3 * 3`.
-/

@[exercise "3a" 6]
theorem sum_le_28
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4)
    (hw : abs w ≤ 3) :
    abs (x - y + z) + w^2 ≤ 28 := by
  sorry

end absolute_value_exercise
