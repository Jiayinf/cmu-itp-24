import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Find
import CmuItp24.Autograde

namespace assignment5

/-
EXERCISE 1.

A function `F : Set α → Set α` is called a *monotone operator* if for every
pair of sets `s ⊆ t`, we have `F s ⊆ F t`.

Every such operator has a *least fixed point*, i.e. a set `s` satisfying:
- `F s = s`
- For every `t`, if `F t = t`, then `s ⊆ t`.

This exercise has you prove that fact. In fact, the least fixed point is
the intersection of all sets `s` such that `F s ⊆ s`.

This theorem, or the generalization to monotone operators on a complete lattice,
is called *Tarski's theorem* or the *Knaster-Tarski Theorem*. Feel free to use
Google to find more information.
-/

namespace monotone_set_operator
open Set

-- You will need these. The full names are `Set.mem_sInter`, etc.
#check mem_sInter
#check subset_sInter
#check subset_sInter_iff

variable {α : Type*}

def A : Set ℕ := {1, 2}
def S : Set (Set ℕ) := { t | A ⊆ t }

example : ⋂₀ S ⊆ A :=
  λ x hx => hx A (λ a ha => ha)



def lfp (F : Set α → Set α) := ⋂₀ { t | F t ⊆ t }

variable {F : Set α → Set α}
-- The monotonicity assumption:
variable (monoF : ∀ ⦃s t⦄, s ⊆ t → F s ⊆ F t)

/-
This follows immediately from the definition of `lfp F`.
-/
@[exercise "1a" 3]
lemma aux0 {s : Set α} (h : F s ⊆ s) : lfp F ⊆ s :=
  λ x hx => hx s h

/-
Lemmas `aux1` and `aux2` and theorem `lfp_fixed_point` need the monotonicity
assumption. After you prove `aux1`, you have to write `aux1 monoF` to use it
in a later theorem.
-/
section
include monoF

/-
To show this next statement, it suffices to show that `F (lfp F)` is contained
in every set `t` such that `F t ⊆ t`. So suppose `t` has this property.
Then by `aux0`, `lfp F ⊆ t`, and by monotonicity, we have `F (lfp F) ⊆ F t ⊆ t`.
-/
@[exercise "1b" 4]
lemma aux1 : F (lfp F) ⊆ lfp F := by
  unfold lfp
  intro x hx
  intro t ht
  have h1 : F (lfp F) ⊆ F t := monoF (aux0 ht)
  have h2 : F t ⊆ t := ht
  exact h2 (h1 hx)

-- Hint: The remaining exercise 1 proofs below can be done in at most three
-- lines each.

/- To show this, use `aux0`. -/
@[exercise "1c" 2]
lemma aux2 : lfp F ⊆ F (lfp F) := by
  apply aux0
  apply monoF
  have h1 : F (lfp F) ⊆ lfp F := aux1 monoF
  apply h1


/- Follows from `aux1` and `aux2`. -/
@[exercise "1d" 2]
theorem lfp_fixed_point : F (lfp F) = lfp F := by
  ext y
  constructor
  apply aux1 monoF
  apply aux2 monoF

end

@[exercise "1e" 2]
theorem lfp_least_fixed_point (s : Set α) (h : F s = s) : lfp F ⊆ s := by
  have h1 : F s ⊆ s := by rw [h]
  unfold lfp
  intro x hx
  apply hx
  exact h1

end monotone_set_operator

/-
EXERCISE 2.

A `complete lattice` is a partial order such that every subset has a greatest
lower bound (`Inf`) and a least upper bound (`Sup`). In fact, the existence
of either implies the other.

The proofs above carry over to this more general setting, if you replace
`α` by `Set α`, `⊆` by `≤`, `⋂₀` by `sInf`, and make some small adjustments
to the proof.

Really, start by cutting and pasting the proofs above.
-/

namespace monotone_operator

#check le_sInf
#check le_sInf_iff
#check sInf_le

variable {α : Type*} [CompleteLattice α]

def lfp (F : α → α) := sInf { s | F s ≤ s }

variable {F : α → α} (monoF : ∀ ⦃s t⦄, s ≤ t → F s ≤ F t)

@[exercise "2a" 2]
lemma aux0 {s : α} (h : F s ≤ s) : lfp F ≤ s := by
  apply sInf_le
  exact h

section
include monoF

@[exercise "2b" 2]
lemma aux1 : F (lfp F) ≤ lfp F := by
  apply le_sInf
  intro t ht
  have h1 := monoF (sInf_le ht)
  exact le_trans h1 ht

@[exercise "2c" 1]
lemma aux2 : lfp F ≤ F (lfp F) := by
  apply aux0
  apply monoF
  apply aux1
  apply monoF

@[exercise "2d" 1]
theorem lfp_fixed_point : F (lfp F) = lfp F := by
  apply le_antisymm
  exact aux1 monoF
  exact aux2 monoF

end

@[exercise "2e" 2]
theorem lfp_least_fixed_point (s : α) (h : F s = s) : lfp F ≤ s := by
  apply aux0
  rw [h]

end monotone_operator

/-
EXERCISE 3.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`B n = ⋃ i < n, A i`. Then the sequence `B 0, B 1, B 2, ...` is a monotone
sequence with the same union.
-/

namespace set_sequences

variable {α : Type*}
variable (A B : ℕ → Set α)
variable (B_def : ∀ n, B n = ⋃ i < n, A i)

/-
A (bounded) union corresponds to a (bounded) existential quantifier.
Lean's simplifier, `simp`, will carry out the logical translations.
-/

example (x : α) : (x ∈ ⋃ i, A i) ↔ ∃ i, x ∈ A i := by
  simp

example (x : α) (n : ℕ) : (x ∈ ⋃ i < n, A i) ↔ ∃ i < n, x ∈ A i := by
  simp

/-
Remember you can also use `simp at h` to simplify a hypothesis `h`.

Mathlib formalization style discourages "non-terminal" calls to `simp`, i.e.
ones which don't close a goal. I'll eventually explain why in class.
For these exercises, however, you can use `simp` freely.
-/

-- This might be helpful to you:
example (i : ℕ) : i < i + 1 := Nat.lt_succ_self _

include B_def

@[exercise "3a" 4]
theorem monotone_B : ∀ i j, i ≤ j → B i ⊆ B j := by
  intros i j hij
  rw [B_def, B_def]
  intro x hx
  simp at hx
  simp
  obtain ⟨ i', hi', hxi'⟩ := hx
  exact ⟨ i', lt_of_lt_of_le hi' hij, hxi' ⟩

@[exercise "3b" 6]
theorem Union_B_eq_Union_A : (⋃ i, B i) = (⋃ i, A i) := by
  ext x
  simp [B_def]
  constructor
  intro ⟨n, ⟨i, hi, hx⟩⟩
  exact ⟨i, hx⟩
  intro ⟨i, hx⟩
  exact ⟨i + 1, i, Nat.lt_succ_self i, hx⟩

end set_sequences

/-
EXERCISE 4.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`C n = A n \ (⋃ i < n, A i)`. Then whenever `i ≠ j`, the sets `C i` and `C j` are
disjoint, but the sequence still has the same union.
-/

namespace set_sequences

variable {α : Type*}
variable (A C : ℕ → Set α)
variable (C_def : ∀ n, C n = A n \ (⋃ i < n, A i))

-- This may be useful.
#check Set.eq_empty_of_forall_not_mem

/-
Use the lemma `aux` below to show that if `x` is in some `A i`, then there
is a least `i` with that property.
-/
section
open Classical

lemma aux {A : ℕ → Set α} {x : α} (h : ∃ i, x ∈ A i) :
    ∃ i, x ∈ A i ∧ ∀ j < i, x ∉ A j :=
  Subtype.existsOfSubtype (Nat.findX h)

end

include C_def

@[exercise "4a" 4]
theorem disjoint_C_of_lt : ∀ i j, i < j → C i ∩ C j = ∅ := by
  intros i j hlt
  apply Set.eq_empty_of_forall_not_mem
  -- Assume x is in C i ∩ C j
  intro x hx
  simp at hx
  rcases hx with ⟨hxi, hxj⟩
  -- From the definition of C i, we know x ∈ A i and x ∉ ⋃ k < i, A k
  -- From the definition of C j, we know x ∈ A j and x ∉ ⋃ k < j, A k
  rw [C_def] at hxi hxj
  rcases hxi with ⟨hxi_A, hxi_not⟩
  rcases hxj with ⟨_, hxj_not⟩
  simp at hxi_not
  simp at hxj_not
  -- x ∈ A i but also x ∈ A j. Use i < j to derive a contradiction.
  have h1 : x ∉ A i := by
    apply hxj_not
    apply hlt
  exfalso
  exact h1 hxi_A

@[exercise "4b" 6]
theorem Union_C_eq_Union_A : (⋃ i, C i) = (⋃ i, A i) := by
  ext y
  constructor

  intros hy
  simp at hy
  rcases hy with ⟨i, hyi⟩
  rw [C_def] at hyi
  simp at hyi
  rcases hyi with ⟨hy1, hy2⟩
  simp
  use i
  intro hx
  simp at hx

  have h3: ∃ i, y ∈ A i ∧ ∀ x < i, y ∉ A x := by
    apply aux hx
  rcases h3 with ⟨i, b⟩
  rcases hx with ⟨j, hxj⟩
  simp
  use i
  rw [C_def]
  simp
  exact b

end set_sequences
