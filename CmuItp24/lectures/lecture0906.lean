import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

Remember: I add a "pre" version of each lecture to the repository before class, and I add a
 "post" version after.

Assignment 2 is due at midnight, and we'll post assignment 3 soon.

Late policy: 10% each day for up to 2 days.

If you get a message that says "Imports are out of date and must be rebuilt;
use the "Restart File" command in your editor," press the blue "Restart File" button.

When there are goals remaining, the error message is usually on the associated ``by``.
Sometimes error messages appear on the next command or theorem.
Putting a ``done`` tactic at the end of the proof helps localize the errors.

# Recap

We're essentially done with Chapter 2 of Mathematics in Lean.

# Agenda

Let's start on Chapter 3!

-/

section

#check gcd_dvd_left
#check gcd_dvd_right
#check dvd_gcd

example (m n : ℕ) : gcd m n = gcd n m := by
  apply dvd_antisymm
  · apply dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left
  · apply dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left

example (m n : ℕ) : gcd m n = gcd n m := by
  apply dvd_antisymm
  repeat
  { apply dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left }

example (m n : ℕ) : gcd m n = gcd n m := by
  have h : ∀ m n : ℕ, gcd m n ∣ gcd n m := by
    intro m n
    apply dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left
  apply dvd_antisymm (h m n) (h n m)

end

section
variable {α : Type*} [Lattice α]

#check le_inf
#check inf_le_left
#check inf_le_right

example (m n : α) : m ⊓ n = n ⊓ m := by
  sorry

end

/-
Our goal now is to talk about how to handle logical connectives.

I will say things like:

"To prove 'A and B', is suffices to prove A and then to prove B."

"If you know 'A and B', you can use A and you can use B."

The point is, to communicate these intentions to Lean, we have to give names to
these actions.

Analogies:

- Learning grammar.
- Learning Latex.

Everything I go over here is in *Mathematics in Lean*. There is also a cheatsheet:

  https://raw.githubusercontent.com/madvorak/lean4-cheatsheet/main/lean-tactics.pdf

The list:

→       \to, \r       if ... then         implication
∀       \all          for all             universal quantifier
∃       \ex           there exists        existential quantifier
¬       \not, \n      not                 negation
∧       \and          and                 conjunction
↔       \iff, \lr     if and only if      bi-implication
∨       \or           or                  disjunction
False                 contradiction       falsity
True                  this is trivial!    truth

Remember that a goal in Lean is of the form

  1 goal
  x y : ℕ,
  h₁ : Prime x,
  h₂ : ¬Even x,
  h₃ : y > x
  ⊢ y ≥ 4

The stuff before the `⊢` is called the *context*, or *local context*. The facts
there are called *hypotheses* or *local hypotheses*.

The stuff after the `⊢` is also called the *goal*, or the *target*.

A common theme:

- Some tactics tell us how to *prove* a goal involving the connective.
  (Logician's terminology: "introduce" the connective.)

- Some tactics tell us how to *use* a hypothesis involving the connective.
  (Logician's terminology: "eliminate" the connective.)

Summary:

→       if ... then       `intro`, `intros`     `apply`, `have h₃ := h₁ h₂`
∀       for all           `intro`, `intros`     `apply`, `specialize`,
                                                  `have h₂ := h₁ t`
∃       there exists      `use`                 `rcases`
¬       not               `intro`, `intros`     `apply`, `contradiction`
∧       and               `constructor`          `rcases`, `h.1` / `h.2`,
                                                  `h.left` / `h.right`
↔       if and only if    `constructor`          `rcases`, `h.1` / `h.2`,
                                                  `h.mp` / `h.mpr`, `rw`
∨       or                `left` / `right`      `rcases`
false   contradiction                           `contradiction`, `exfalso`
true    this is trivial!  `trivial`

Also, for proof by contradiction:

  Use the `by_contra` tactic.

There are lots of other tactics and methods. But these are all you need to deal
with the logical connectives.

Another theme: sometimes the logical structure is hidden under a definition.
For example:

  `x ∣ y`   is existential
  `s ⊆ t`  is universal

Lean will unfold definitions as needed.
-/

/-!
### Implication and the universal quantifier
-/

theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variable (a b c d : ℝ)
variable (h₁ : a ≤ b)
variable (h₂ : c ≤ d)

#check my_add_le_add a b
#check my_add_le_add a b c d
#check my_add_le_add a b c d h₁
#check my_add_le_add a b c d h₁ h₂
#check my_add_le_add _ _ _ _ h₁ h₂
#check my_add_le_add _ _ _ _ h₁

end

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variable (a b c d : ℝ)
variable (h₁ : a ≤ b)
variable (h₂ : c ≤ d)

#check my_add_le_add' h₁ h₂
#check @my_add_le_add' a b c d h₁ h₂
#check my_add_le_add' (z := c) h₁

end

def FnUb (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

section

variable {f g : ℝ → ℝ} {a b : ℝ}

-- demonstrate variations on `apply`, `have`, and `specialize`
-- `dsimp` helps clarify the goal

theorem fnUb_add (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (f + g) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb

example (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (f + g) (a + b) := by
  intro x
  apply add_le_add
  · exact hfa x
  · exact hgb x

example (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (f + g) (a + b) := by
  intro x
  apply add_le_add (hfa x) (hgb x)

example (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (f + g) (a + b) :=
  fun x => add_le_add (hfa x) (hgb x)

example (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (f + g) (a + b) := by
  intro x
  specialize hfa x
  specialize hgb x
  exact add_le_add hfa hgb

end

/-
The existential quantifier
-/

-- demonstrate `use` and `norm_num`
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 2.5
  norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

-- set_option pp.notation false

example : 5 ∣ 20 := by
  use 4

example : 5 ∣ 20 := by
  norm_num

-- demonstrate `cases` and `use`, and use `FnUb_add`

section

def FnHasUb (f : ℝ → ℝ) := ∃ a, FnUb f a

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) :
    FnHasUb (f + g) := by
  rcases ubf with ⟨a, ha⟩
  rcases ubg with ⟨b, hb⟩
  use a + b
  apply fnUb_add ha hb

/-
Finding theorems in the library:

o Try to guess the name and use tab completion.

  https://leanprover-community.github.io/contribute/naming.html

o You can use the API documentation on the mathlib web pages.

  https://leanprover-community.github.io/mathlib_docs/

o You can browse mathlib on Github.

o Use `exact?`, `apply?`, `rw?`

o Use `loogle` in VS Code.

o Use moogle: https://www.moogle.ai/

o Use LeanSearch: https://leansearch.net/

-/

example (a : ℝ) : 0 ≤ a^2 := by
  -- exact?
  -- rw?
  -- apply?
  sorry

open Real

example (a b c : ℝ) (h : a ≤ b) : c - exp b ≤ c - exp a := by
  -- apply?
  -- rw?
  sorry
