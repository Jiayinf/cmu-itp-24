import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Recap from last time

Course overview
- interactive theorem proving
- this course:
- Lean:
  - expressions
  - types
  - #check
  - #eval

To do:
- Make sure you find the course on Piazza and Gradescope
- Do assignment 1 on Piazza
  - install Git
  - install Lean / Mathlib / Mathematics in Lean
  - set up a Github account and send us your username
  - Fetch the user repository

# Agenda

- Using MIL and the course repository
- Finish the Lean demo
- Getting started with MIL

# Using MIL and the course repository

Once you fetch MIL, we recommend making a copy of the MIL folder
(use copy/paste and name it whatever you want).
You can then edit the files there and leave the originals.

There are examples and exercises, and separate solution files.

They are meant to be read side by side with the textbook.

Every once in a while, we will recommend updating the textbook.
Do this from a terminal in the top folder:

- `git pull`
- `lake exe cache get`

We will add lectures and exercises to the course repository.

- `lecture_0828_pre.lean` has the file I will use at the beginning of the lecture.
- `lecture_0828.lean` has the final result.

If you haven't edited the files, you can fetch with `git pull`.
(If you have, you can do `git commit -am "my changes"` or
`git restore` to undo them, and then `git pull`.)

If we have bumped Mathlib, you can fetch the precompiled files with
`lake exe cache get`.

If you don't do this, you may get "the yellow bars from hell".

There is no harm to doing `lake exe cache get` to be safe.
-/

#check Nat
#check 3
#check 2 + 2 = 4
#check show 2 + 2 = 4 from rfl
#check @id (2 + 2 = 4) rfl

#eval 2 + 2

def foo := 2

theorem foo_equals_2 : foo = 2 := rfl

/-
Some more interesting examples.
-/

def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => (2 * n + 1) + f n

example : Monotone (fun x : ℝ => x + 3) := by
  sorry


/-
Let's get started with MIL!
-/

/-
Rewrite and apply
-/

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  sorry

example (a b c d e : ℕ) (h1 : a = b + 1) (h2 : d = c + a) (h3 : e = b + c) : d = e + 1 := by
  sorry

-- see also the tactic `nth_rewrite`.
-- https://leanprover-community.github.io/mathlib_docs/tactics.html#nth_rewrite%20/%20nth_rewrite_lhs%20/%20nth_rewrite_rhs

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

#check @inv_mul_cancel
#check @mul_one
#check @one_mul
#check @mul_assoc

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z = y * (y * z) * (y * z) * z
  · sorry
  have h2 : z * y = y * (y * z) * (y * z) * z
  · sorry
  sorry

#check @mul_left_cancel

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z * (y * z) = y * z * (z * y)
  · sorry
  sorry

end

/-
Integer ModEq
-/

#check Int.ModEq
#check @Int.ModEq.refl
#check @Int.ModEq.symm
#check @Int.ModEq.trans
#check @Int.ModEq.add
#check @Int.ModEq.add_left

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
