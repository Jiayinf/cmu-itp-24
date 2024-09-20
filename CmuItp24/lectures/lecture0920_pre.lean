import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Announcements

We'll post Assignment 5 soon.

# Recap

We finished talking about sets and started talking about functions.

-/


/-
Functions
-/

variable {α β I : Type*}

section function_variables
open Set Function

variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)
variable (A : I → Set α)
variable (B : I → Set β)

#check f '' s
#check image f s
#check f ⁻¹' u    -- type as \inv' and then hit space or tab
#check preimage f u

example : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl
example : f ⁻¹' u = {x | f x ∈ u} := rfl

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  sorry

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  sorry

example : s ⊆ f ⁻¹' (f '' s) := by
  sorry


/-
Exercises
-/

example : f '' s ⊆ u ↔ s ⊆ f ⁻¹' u :=
sorry

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s :=
sorry

example : f '' (f⁻¹' u) ⊆ u :=
sorry

example (h : Surjective f) : u ⊆ f '' (f⁻¹' u) :=
sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
sorry

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
sorry

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
sorry

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
sorry

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
sorry

end function_variables

/-
Mathlib also has bounded quantifiers.
-/

example (P : ℕ → Prop) (n m : ℕ) (h : m < n) : (∀ x < n, P x) → ∀ x < m, P x := by
  sorry

example (P : ℕ → Prop) (s t : Set ℕ) (h : s ⊆ t) :
    (∀ x ∈ t, P x) → ∀ x ∈ s, P x := by
  sorry

/-
Similarly, bounded unions:
-/

section set_variables

variable (A : ℕ → Set α)

example (s t : Set ℕ) (h : s ⊆ t) : (⋂ i ∈ t, A i) ⊆ (⋂ i ∈ s, A i) := by
  sorry

/-
Also, unions and intersections of sets:
-/

example (s : Set (Set ℕ)) (t : ℕ) : t ∈ ⋃₀ s ↔ ∃ u ∈ s, t ∈ u := by
  sorry
example (s : Set (Set ℕ)) (t : ℕ) : t ∈ ⋂₀ s ↔ ∀ u ∈ s, t ∈ u := by
  sorry

end set_variables

section function_variables
open Function

/-
There is a lot more in *Mathematics in Lean*.
There is a discussion of injectivity, more exercises on images and ranges,
and a discussion of inverses.

But we will close with on last exercise. Remember that `Surjective f`
says `∀ y, ∃ x, f x = y`.
-/

theorem Cantor : ∀ f : α → Set α, ¬ Surjective f := by
  intros f surjf
  let S := { i | i ∉ f i}
  sorry

end function_variables
