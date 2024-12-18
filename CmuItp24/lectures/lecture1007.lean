import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 7 is online.

# Recap

Last time:

- more about structural induction.
- discuss assignment 7.

# Plans

This week:

- algebraic structures and the algebraic hierarchy
- the final project and a tour of mathlib
- more on finsets and combinatorial reasoning

The first project will be due Friday, November 8.

On Friday, October 25: we will ask you to turn in a start on the final project:
a statement of the main theorem and definitions, an outline of the proof, etc.

-/

/-
Moving on to the algebraic hieararchy, consider some common structures:

A *partially ordered set* consists of a set P and a binary relation
≤ on that is transitive and reflexive.

A *group* consists of a set G with an associative binary operation, an identity
element 1, and a function g ↦ g⁻¹  that returns an inverse for each g in G
A group is abelian or commutative if the operation is commutative.

A *lattice* is a partially ordered set with meets and joins.

A *ring* consists of an (additively written) abelian group (R, +, 0, x ↦ -x)
together with an associative multiplication operation ⬝ and an identity 1,
such that multiplication distributes over addition. A ring is commutative if the multiplication is commutative.

A *metric space* consists of a set X and a function d : X × X → ℝ
such that the following hold:
- d(x, y) ≥ 0 for every x and y in X.
- d(x, y) = 0 iff x = y.
- d(x, y) = d(y, x) for every x and y in X.
- d(x, z) ≤ d(x, y) + d(y, z) for every x, y, and z in X.

A *toupological space* consists of a set X and a collection T
of subsets of X, called the open subsets of X, such that the
following hold:
- The empty set and X are open.
- The intersection of two open sets is open.
- An arbitrary union of open sets is open.

In these cases, there is one distinguished set (or type), namely, the *carrier*.
But sometimes there is more than one. For example, a vector space over a field
depends on both the set of vectors and the set of elements of the field
(though you can view the field as a *parameter* in this definition.)

What do we need?
- Generic notation: +, *, ≤, wherever they make sense.
- Generic definitions: `min`, `max`, `inf`, `sup`, `Continuous` etc. wherever
  they make sense.
- Generic facts: `mul_comm`, `le_of_lt_of_le` wherever they make sense.
- Structures vs. instances: ℝ is an instance of a ring, and a partial order
    (and lots of other things).
- Inheritance: every field is a ring, every ring includes an additive group,
    every metric space has a natural topology.
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

- A structure is a `structure`, i.e. data and properties bundled together.

  In Mathlib, we generally use a `partially bundled` encoding, e.g. if
  `α` is a type, `Group α` encodes a group structure on `α`.
-/

#check PartialOrder
namespace ex1

structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

structure Point2 where
  x : ℝ
  y : ℝ
  z : ℝ
  hx : 0 ≤ x
  hy : 0 ≤ y
  hz : 0 ≤ z

structure PartialOrder (α : Type*) where
  le : α → α → Prop
  rfl : ∀ x : α, le x x
  trans : ∀ x y z : α, le x y → le y z → le x z
  antisymm : ∀ x y : α, le x y → le y x → x = y

def bar : PartialOrder ℝ where
  le := fun x y => x ≤ y
  rfl := sorry
  trans := sorry
  antisymm := sorry

variable (P : Type) (Pstruct : PartialOrder P)

#check Pstruct.le
#check Pstruct.rfl

example (x : P) : Pstruct.le x x := Pstruct.rfl x

structure Group (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

variable (G : Type) (Gstruct : Group G)

#check Gstruct.mul
#check Group.mul

end ex1

#check mul_comm
/-
- Implicit arguments: a function like `mul` (with notation `*`) or a
  theorem `mul_comm` has implicit arguments for the relevant structure.
  Some implicit arguments (those marked with `{ }`) are filled in by
  pattern matching. For example, theorem `foo {α : Type} (x y z : α) ...`
  can generally leave `α` implicit because Lean can figure it out
  from the arguments, `x`, `y`, and `z`. But algebraic structure is different!
-/

def myident {α : Type*} (x : α) := x

#check myident 4
#check myident [1, 2, 3]

set_option pp.explicit true in
#check myident [1, 2, 3]

#check @myident ℕ
#check @myident ℕ 4
#check myident
#check myident (α := ℕ)
#check @myident

set_option pp.explicit true in
#check myident 4

def foo := myident [(1 : ℤ), 2, 3, 4]

set_option pp.explicit true in
#print foo

/-

- Type class inference: implicit arguments marked by square brackets, like so
  `[Group α]`. We can register instances of groups with the `instance`
  command, and Lean can search through registered instances to find the group
  structure.

Everything else comes from the underlying logic. For example, constructions
of algebraic structure from others are just functions.
-/

#check Mul.mul   -- Mul.mul.{u} {α : Type u} [self : Mul α] : α → α → α

section
variable (x y : ℝ)

set_option pp.explicit true
#check Mul.mul x y

example : x * y = Mul.mul x y := rfl

end

namespace ex2

class PartialOrder (α : Type*) where
  le : α → α → Prop
  rfl : ∀ {x : α}, le x x
  trans : ∀ {x y z : α}, le x y → le y z → le x z

instance : PartialOrder ℝ where
  le := fun x y => x ≤ y
  rfl := sorry
  trans := sorry

#check PartialOrder.le
example (x : ℝ) : PartialOrder.le x x ↔ x ≤ x := by
  rfl

variable {P : Type} [PartialOrder P]
variable (x y : P)

set_option pp.explicit true in
#check PartialOrder.le x y

example : PartialOrder.le x x := PartialOrder.rfl

open PartialOrder

example : le x x := rfl

instance (P : Type) [PartialOrder P] : LE P := ⟨PartialOrder.le⟩

#check x ≤ x

example : x ≤ x := rfl

class Group (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

variable {G : Type} [Group G]

end ex2
