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
#check ℕ
#check 3
#check 2 + 2 = 4
#check show 2 + 2 = 4 from rfl
#check @id (2 + 2 = 4) rfl

#eval 2 + 2

def foo : ℕ := 2

#check foo
#print foo
#eval foo

theorem foo_equals_2 : foo = 2 := rfl

#check foo_equals_2


/-
Some more interesting examples.
-/

def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => (2 * n + 1) + f n

#eval f 0
#eval f 1
#eval f 2
#eval f 3

#eval List.range 10 |>.map f

theorem f_equals : ∀ n, f n = n^2 := by
  intro n
  induction' n with n ih
  · simp [f]
  · simp [f, ih]; ring

#check f
#check f_equals

example : Monotone (fun x : ℝ => x + 3) := by
  intro x1 x2 h
  dsimp
  linarith

example : Monotone (fun x : ℝ => x + 3) := by
  intro x1 x2 h
  simpa


/-
Let's get started with MIL!
-/

/-
Rewrite and apply
-/

#check mul_assoc
#check mul_comm

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b, mul_assoc b a c]

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  rw [mul_comm a, mul_assoc]

example (a b c d e : ℕ) (h1 : a = b + 1) (h2 : d = c + a) (h3 : e = b + c) : d = e + 1 := by
  rw [h2, h1, h3, add_comm b c, add_assoc]

theorem bar (a b c d e : ℕ) (h1 : a = b + 1) (h2 : d = c + a) (h3 : e = b + c) : d = e + 1 := by
  rw [h1] at h2
  rw [h2, h3, ← add_assoc, add_comm c b]

#check bar
-- see also the tactic `nth_rewrite`.
-- https://leanprover-community.github.io/mathlib_docs/tactics.html#nth_rewrite%20/%20nth_rewrite_lhs%20/%20nth_rewrite_rhs
