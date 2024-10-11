import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 6 will be online this afternoon.

I will not be here on Monday, September 30; Wojciech will do the lecture.

# Agenda

Today: start talking about algebraic structures, following Chapter 6.

Monday:
- more about induction on the natural numbers
- induction on other structures.

After that, until fall break:
- finite sets
- more about induction
- more algebra
- some number theory
- some discrete math or combinatorics
- exploring Mathlib
- talking about the projects

- Fall break!

- First project (3 weeks)
- Second project (4 weeks)
-/

-- To make sure you can use `linarith`,
-- use `import Mathlib.Tactic`.

#check lt_trans
#check le_trans
#check lt_of_le_of_lt
#check lt_of_lt_of_le

example (m n k : ℕ) (h : m < n + 1) (h' : n + 1 ≤ k) : m < k := by
  -- linarith
  omega

/-
Structures, following MIL.
-/

noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point

section
variable (p : Point)

#check p.x
#check p.y
#check p.z

end

#check Point.ext
#check Point.ext_iff

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  -- apply Point.ext hx hy hz
  ext <;> assumption

-- do the lightbulb trick!

def myPoint1 : Point where
  x := 4
  y := 2
  z := 7

#check myPoint1
#print myPoint1

def myPoint2 : Point :=
  {  y := 2, x := 4, z := 7 }

def myPoint3 : Point := ⟨4, 2, 7⟩

def myPoint4 : Point where
  x := 4
  y := 2
  z := 7

namespace Point

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

def add' (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

end Point

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> (dsimp; rw [add_comm])

example (a b : Point) : add a b = add b a := by
  simp [Point.ext_iff, add, add_comm]

example (a b : Point) : add a b = add b a := by
  ext <;> simp [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x := by
  rfl

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  ext <;> simp [add, add_assoc]

def smul (r : ℝ) (a : Point) : Point where
  x := r * a.x
  y := r * a.y
  z := r * a.z

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
  ext <;> simp [add, smul, mul_add]

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

def myPoint5 : StandardTwoSimplex where
  x := 1
  y := 0
  z := 0
  x_nonneg := by simp
  y_nonneg := by simp
  z_nonneg := by simp
  sum_eq := by simp

section
variable (a : StandardTwoSimplex)

#check a.x
#check a.x_nonneg

end

namespace StandardTwoSimplex

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [←a.sum_eq]; abel

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := by
    linarith [a.x_nonneg, b.x_nonneg]
    -- apply div_nonneg
    -- apply add_nonneg
    -- exact a.x_nonneg
    -- exact b.x_nonneg
    -- norm_num
  y_nonneg := by
    linarith [a.y_nonneg, b.y_nonneg]
  z_nonneg := by
    linarith [a.z_nonneg, b.z_nonneg]
  sum_eq := by
    --field_simp
    --have h1 := a.sum_eq
    --have h2 := b.sum_eq
    linarith [a.sum_eq, b.sum_eq]
    --done

end

end StandardTwoSimplex

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n := sorry

end StandardSimplex

/-
Moving on to the algebraic hieararchy, we'll take a look at the structures
in the textbook:

- partial orders
- groups
- lattices
- rings
- ordered rings
- metric spaces
- topological spaces

In this cases, there is one distinguished set (or type), namely, the *carrier*.
But sometimes there is more than one.

What do we need?
- Generic notation: +, *, ≤, wherever they make sense.
- Generic definitions: `min`, `max`, `inf`, `sup`, etc. wherever they make sense.
- Generic facts: `mul_comm`, `le_of_lt_of_le` wherever they make sense.
- Structures vs. instances: ℝ is an instance of a ring, and a partial order
    (and lots of other things).
- Inheritance: every field is a ring, every ring includes an additive group.
- Constructions: if `G` and `H` are groups, so are `G × H` and the group
  of automorphisms of `G`. Similarly, for every `n`, `ℝ^n` is a vector space.

Terminological distinction:
- I'll use "structure" for the abstract *class*, i.e. the group structure,
  the ring structure, etc.
- I'll use "instance" for a concrete instance, e.g. the (ℝ, +, *, 0, 1, ...)
  is an instance of the ring structure

Roughly, we have

  Group : Type
  G : Group

so Group is the structure and G is the instance.

In ordinary mathematical language, the word "structure" is used sometimes for
one and sometimes for the other.

The key ideas:

- A structure is a `Structure`, i.e. data and properties bundled together.

  In Mathlib, we generally use a `partially bundled` encoding, e.g. if
  `α` is a type, `Group α` encodes a group structure on `α`.

- Implicit arguments: a function like `mul` (with notation `*`) or a
  theorem `mul_comm` has implicit arguments for the relevant structure.
  Some implicit arguments (those marked with `{ }`) are filled in by
  pattern matching. For example, theorem `foo {α : Type} (x y z : α) ...`
  can generally leave `α` implicit because Lean can figure it out
  from the arguments, `x`, `y`, and `z`. But algebraic structure is different!
  We use...

- Type class inference: implicit arguments marked by square brackets, like so
  `[Group α]`. We can register instances of groups with the `instance`
  command, and Lean can search through registered instances to find the group
  structure.

Everything else comes from the underlying logic. For example, constructions
of algebraic structures from others are just functions.
-/
