import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 7 in posted. It may be the last weekly assignment!

# Recap

Last time:

- finsets (briefly).
- sums and products.
- more about induction on the natural numbers.

# Agenda

- more about structural induction.
- discuss assignment 7.
- back to algebraic structures.

# Correction

Last time, I said you need to open the namespace `Big_Operators`
to use notation for sums and products. I was wrong! That is no
longer the case.

-/

/-
Another style of writing proofs by structural induction.
-/

section

variable {α β γ : Type*}
variable (as bs cs : List α)
variable (a b c : α)

open List

theorem append_nil' : as ++ [] = as := by
  induction' as with a as ih
  . rfl
  . rw [cons_append, ih]

-- do the lightbulb trick!

#eval map (fun n => n^2) [1, 2, 3, 4, 5]

def map' (f : α → β) : List α → List β
  | []      => []
  | a :: as => f a :: map' f as

#eval map' (fun n => n^2) [1, 2, 3, 4, 5]

theorem map'_map' (f : α → β) (g : β → γ) (as : List α) :
    map' g (map' f as) = map' (g ∘ f) as := by
  induction' as with a as ih
  . rfl
  .  simp [map', ih]


/-
Go over assignment 7.
-/

/-
Reversing a list.
-/

def bad_reverse : List α → List α
  | []      => []
  | a :: as => concat (bad_reverse as) a

/-- `reverse_aux as acc` reverses `as` and appends `acc` -/
def reverse_aux : List α → List α → List α
  | [],      acc => acc
  | a :: as, acc => reverse_aux as (a :: acc)

def reverse' (as : List α) := reverse_aux as []

theorem reverse_aux_append (as bs cs : List α) :
    reverse_aux (as ++ bs) cs = reverse_aux bs (reverse_aux as cs) := by
  -- Can't prove this without `generalizing cs`!
  sorry

theorem reverse_aux_append' (as bs cs : List α) :
    reverse_aux as (bs ++ cs) = (reverse_aux as bs) ++ cs := by
  sorry

theorem reverse'_append (as bs : List α) :
    reverse' (as ++ bs) = reverse' bs ++ reverse' as := by
  sorry

end

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
of algebraic structure from others are just functions.
-/
