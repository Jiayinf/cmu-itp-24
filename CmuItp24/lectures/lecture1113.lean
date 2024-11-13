import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
# Announcements

The final project is due on Friday, December 6, the last day of class.

Don't put work off until the last minute!

Tell us by Monday, November 11 what you plan to do.

For the rest of the semester:
  lectures on Monday and Wednesday
  extra office hour on Friday

Office hours for the rest of the semester:

  Monday, 2-3 (Jeremy)
  Tuesday, 3-4 (Wojciech)
  Wednesday, 11-12 (Wojciech)
  Wednesday, 3:30-4:30 (Eric)
  Thursday, 4-5 (Eric)
  Friday, 12-1 (Jeremy)

# Agenda

Today: verifying programs in Lean
Monday: metaprogramming in Lean
Wednesday: back to foundations

(I still owe you: inductive datatypes, Lean axioms.)

-/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n + 1)

#eval fib 20

def fib₁_aux : Nat → Nat × Nat
  | 0 => (0, 1)
  | n+1 => let (a, b) := fib₁_aux n
           (b, a+b)

def fib₁ (n : Nat) := fib₁_aux n |>.1

#eval fib₁ 20

theorem fib_eq_fib₁_aux (n : Nat) :
    fib₁_aux n = (fib n, fib (n + 1)) := by
  induction' n with n ih
  . rfl
  rw [fib₁_aux, ih]; rfl

@[csimp]
theorem fib_eq_fib₁ : fib = fib₁ := by
  ext n
  rw [fib₁, fib_eq_fib₁_aux]

def fib₂ (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [0:n] do
    let temp := a
    a := b
    b := temp + b
  return a

#eval fib₂ 20

def fib₃_aux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n+1, a, b => fib₃_aux n b (a + b)

def fib₃ (n : Nat) := fib₃_aux n 0 1

#eval fib₃ 100

theorem fib₃_aux_eq (n i : Nat) :
    fib₃_aux n (fib i) (fib (i + 1)) = fib (i + n) := by
  induction' n with n ih generalizing i
  . rfl
  rw [fib₃_aux]
  convert ih (i + 1) using 2
  omega

theorem fib₃_eq : fib₃ = fib := by
  ext n
  rw [fib₃]
  convert fib₃_aux_eq n 0; simp
