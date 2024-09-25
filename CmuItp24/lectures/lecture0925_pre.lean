import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 5 is online.

Plan:

- This week: induction, algebraic structures
- Next two weeks: more algebra, discrete math, tour of Mathlib

- Fall break!

- First project (3 weeks)
- Second project (4 weeks)

# Recap

We're done with Chapter 4.

# Agenda

We'll do Section 5.2 on induction and recursion, and then start talking about algebraic
structures.

-/

/-
A problem from homework 3:
-/

def ApproachesAt (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

theorem approachesAt_comp {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : ApproachesAt f b a) (hg : ApproachesAt g c b) :
    ApproachesAt (g ∘ f) c a := by
  intro ε εpos
  rcases hg ε εpos with ⟨δ', δ'pos, hδ'⟩
  rcases hf δ' δ'pos with ⟨δ, δpos, hδ⟩
  use δ, δpos
  intro x hx
  apply hδ'
  exact hδ _ hx

/-
Moving on to induction.
-/

def fac : ℕ → ℕ
| 0     => 1
| n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  sorry

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  sorry

theorem pow_two_le_fac (n : ℕ) : 2^(n-1) ≤ fac n := by
  sorry

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x in s, f x := rfl
example : s.prod f = ∏ x in s, f x := rfl

example : (range n).sum f = ∑ x in range n, f x := by
  sorry

example : (range n).prod f = ∏ x in range n, f x := by
  sorry

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 := by
  sorry

example (f : ℕ → ℕ) (n : ℕ): ∑ x in range n.succ, f x = (∑ x in range n, f x) + f n := by
  sorry

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 := by
  sorry

example (f : ℕ → ℕ) (n : ℕ): ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n := by
  sorry

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  sorry

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  sorry

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 := by
  sorry

end

inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat

namespace my_nat

def add : my_nat → my_nat → my_nat
| x, zero   => x
| x, succ y => succ (add x y)

def mul : my_nat → my_nat → my_nat
| x, zero   => zero
| x, succ y => add (mul x y) x

theorem zero_add (n : my_nat) : add zero n = n := by
  sorry

theorem succ_add (m n : my_nat) : add (succ m) n = succ (add m n) := by
  sorry

theorem add_comm (m n : my_nat) : add m n = add n m := by
  sorry

theorem add_assoc (m n k : my_nat) : add (add m n) k = add m (add n k) := by
  sorry

theorem mul_add  (m n k : my_nat) : mul m (add n k) = add (mul m n) (mul m k) := by
  sorry

theorem zero_mul (n : my_nat) : mul zero n = zero := by
  sorry

theorem succ_mul (m n : my_nat) : mul (succ m) n = add (mul m n) n := by
  sorry

theorem mul_comm (m n : my_nat) : mul m n = mul n m := by
  sorry

end my_nat

/-
Structures, following MIL.
-/

noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  sorry

structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

namespace Point

def add (a b : Point) : Point :=
  sorry

end Point

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  sorry

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x := by
  sorry

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  sorry

def smul (r : ℝ) (a : Point) : Point :=
  sorry

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
  sorry

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex := sorry

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := sorry
  y_nonneg := sorry
  z_nonneg := sorry
  sum_eq := by sorry

end

end StandardTwoSimplex

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex
