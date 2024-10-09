import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Assignment 7 is online.

# Recap

Last time:

- algebraic structures and the algebraic hierarchy

# Plans

This week:

- finish up algebraic structures
- the final project and a tour of mathlib
- more on finsets and combinatorial reasoning

The first project will be due Friday, November 8.

On Friday, October 25: we will ask you to turn in a start on the final project:
a statement of the main theorem and definitions, an outline of the proof, etc.

-/

class HasTwoThings (α : Type*) where
  thingOne : α
  thingTwo : α
  different : thingOne ≠ thingTwo

#check HasTwoThings.thingOne

namespace HasTwoThings

#check thingOne

variable {α : Type*} [HasTwoThings α]

theorem has_something_else : ∀ x : α, ∃ y : α, x ≠ y := by
  intro x
  by_cases h : x = thingOne
  . use thingTwo
    rw [h]
    exact different
  . use thingOne

end HasTwoThings

instance : HasTwoThings ℕ where
  thingOne := 0
  thingTwo := 1
  different := by simp

instance : HasTwoThings Bool where
  thingOne := true
  thingTwo := false
  different := by simp

open HasTwoThings

#check thingOne
#check (thingOne : ℕ)
#eval (thingOne : ℕ)
#check (thingOne : Bool)
#eval (thingOne : Bool)

example : ∀ x : ℕ, ∃ y, x ≠ y := by
  apply has_something_else

example : ∀ x : ℕ, ∃ y, x ≠ y :=
  has_something_else

example : ∀ x : Bool, ∃ y, x ≠ y := by
  apply has_something_else

example : ∀ x : Bool, ∃ y, x ≠ y :=
  has_something_else

local notation "*^1" => thingOne

notation "*^2" => thingTwo

#check (*^1 : ℕ)

example : *^1 = true := rfl
example : *^1 = 0 := rfl

section
variable {α : Type*} [HasTwoThings α]

example : (*^1 : α) ≠ *^2 := different

end

def thePairOfThings (α : Type*) [HasTwoThings α] : α × α :=
(thingOne, thingTwo)

#check thePairOfThings ℕ
#check thePairOfThings Bool
#eval thePairOfThings ℕ
#eval thePairOfThings Bool

class HasThreeThings (α : Type*) extends HasTwoThings α where
  thingThree : α
  different' : thingThree ≠ thingOne
  different'' : thingThree ≠ thingTwo

example {α : Type} [HasThreeThings α] :
    ∀ x : α, ∃ y, x ≠ y := by
  apply has_something_else

variable (f : ℝ × ℝ → ℝ)

#check Continuous

set_option pp.explicit true in
#check Continuous f

/-
Summary: to declare a new algebraic structure `Foo α`:

- Define the structure using `class`.

- Define notation, write definitions, prove theorems generically, using
  `{α : Type*} [Foo α]`.

- Declare `instance`s. They can be concrete instances, you are can show how
  a more general structure can be interpreted as an instance.

- You can also declare it to be an instance of other things, in which case
  it inherits those theorems.
-/

/-
The first project.

Really: formalize anything.

- You can prove one theorem, or introduce a definition and prove a couple of
  little theorems.
- Go back to any class you have taken and enjoyed, and revisit the material!
- It is o.k. if the result is in Mathlib.
- You might have a more concrete proof, or an alternate proof.
- *Homework exercises* often good for formalization, and often not in mathlib.
- It's o.k. if you overreach and leave some `sorry`s.

Topics:

- elementary number theory
- combinatorics (e.g. concrete mathematics?)
- algebra - group theory, etc.
- probability
- calculus: calculate some integrals?
- topology
- logic (but dealing with bound variables is difficult)
- axiomatic geometry
- linear algebra

If you like computer science, you can port some examples from
- Concrete semantics: http://concrete-semantics.org/
- Software foundations: https://softwarefoundations.cis.upenn.edu/
- Formal reasoning about proofs: http://adam.chlipala.net/frap/

Zulip is a great place to ask questions.

You can also read about formalization projects in other provers (Coq, Isabelle, HOL Light) and port them to Lean.

Examples from last time:

- The metatheory of the simply typed lambda calculus.
  (First project: confluence, second project: normalization)

- Fodor's theorem in set theory.

- definition of Stirling numbers and properties.

- a proof that Fermat numbers are coprime.

- the Lovasz Local Lemma.

- Suppose `f : ℝ → ℝ` satisfies `f 0 = 1` and `f (x + y) = f x * f y` for
every `x` and `y`. Then `f` is an exponential function.

- a direct proof of the Bolzano-Weierstrass theorem.

- Putnam problems.

-/
