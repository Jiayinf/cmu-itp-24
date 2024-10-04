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

Last time, I said you need to open the namespace `BigOperators`
to use notation for sums and products. I was wrong! That is no
longer the case.

-/

/-
A useful idiom:
-/

example (x y z : ℕ) (h : x = y) : z * x = z * y := by
  have : z * x = z * y := by
    rw [h]
  exact this

example (x y z : ℕ) (h : x = y) : z * x = z * y := by
  have := congr_arg (fun u => z * u) h
  -- dsimp at this
  exact this

example (x y z : ℕ) (h : x = y) : z * x = z * y := by
  apply congr_arg (fun u => z * u) at h
  exact h

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

theorem foo : ∀ as : List α, as ++ [] = as
  | []      => by rfl
  | a :: as => by rw [cons_append, foo as]

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

theorem bar (f : α → β) (g : β → γ) :
    ∀ as, map' g (map' f as) = map' (g ∘ f) as
  | [] => by rfl
  | a :: as => by
      -- simp [map', bar f g as]
      simp [map', bar]

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
  induction' as with a as ih generalizing cs
  . rfl
  --simp [reverse_aux]
  --rw [ih]
  simp [reverse_aux, ih]

theorem reverse_aux_append' (as bs cs : List α) :
    reverse_aux as (bs ++ cs) = (reverse_aux as bs) ++ cs := by
  induction' as with a as ih generalizing bs
  . rfl
  rw [reverse_aux, ←cons_append]
  simp only [reverse_aux, ih]

theorem reverse'_append (as bs : List α) :
    reverse' (as ++ bs) = reverse' bs ++ reverse' as := by
  simp only [reverse']
  rw [reverse_aux_append, ←reverse_aux_append', nil_append]

end
