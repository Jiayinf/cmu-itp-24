import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import CmuItp24.Autograde

/-
Once we open the `Finset` namespace, we can use `range` instead of
`Finset.range`, and `sum_range_succ` instead of `Finset.sum_range_succ`,
and so on.
-/

open Finset

/-
EXERCISE 1. Induction on the natural numbers.

For the following exercises, use this definition of the factorial function:
-/

def fac : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fac n


/-
Here is an example of a proof by induction:
-/

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  . simp [fac]
  simp [fac, ih]

/-
This is even shorter. The `<;>` annotation applies the next
tactic to all the goals generated by the previous ones,
and the `*` tells the simplifier to use all the hypotheses
in the context.
-/

example (n : ℕ) : 0 < fac n := by
  induction' n with n ih <;> simp [fac, *]

/-
It may be useful to use the `omega` tactic to proof identities
and inequalities involving the integers. Here is an example:
-/

example (n : ℕ) : fac n - 1 + 1 = fac n := by
  have := fac_pos n
  omega

/-
Prove the following identities.
-/

@[exercise "1a" 5]
theorem ex1a (n : ℕ) : ∑ i in range n, i * fac i = fac n - 1 := by
  sorry

@[exercise "1b" 5]
theorem ex1b (n : ℕ) : ∑ i in range n, (2 * i + 1) = n^2 := by
  sorry

@[exercise "1c" 5]
theorem ex1c (x : ℝ) (n : ℕ) : (∑ i in range n, x^i) * (x - 1) = x^n - 1 := by
  sorry

@[exercise "1d" 5]
theorem ex1d (n : ℕ) :
    3 * (∑ i in range (n + 1), i * (i + 1)) = n * (n + 1) * (n + 2) := by
  sorry


/-
EXERCISE 2. Structural induction.

The following is an inductive definition of binary trees:
-/

inductive BinTree where
  | empty : BinTree
  | node : BinTree → BinTree → BinTree

namespace BinTree

/-
We can define the size and the depth of a binary tree
by recursion.
-/

def size : BinTree → ℕ
  | BinTree.empty => 0
  | BinTree.node l r => size l + size r + 1

def depth : BinTree → ℕ
  | BinTree.empty => 0
  | BinTree.node l r => max (depth l) (depth r) + 1

/-
Here is an important inequality relating the size and the depth.
-/

theorem size_le : ∀ t : BinTree, size t ≤ 2^depth t - 1
  | BinTree.empty => Nat.zero_le _
  | BinTree.node l r => by
      simp only [depth, size]
      calc l.size + r.size + 1 ≤
            (2^l.depth - 1) + (2^r.depth - 1) + 1 := by
              apply Nat.add_le_add_right
              apply Nat.add_le_add
              . apply size_le
              . apply size_le
        _ ≤ (2 ^ max l.depth r.depth - 1) +
              (2 ^ max l.depth r.depth - 1) + 1 := by
            gcongr <;> simp
        _ ≤ 2 ^ (max l.depth r.depth + 1) - 1 := by
            have : 0 < 2 ^ max l.depth r.depth := by simp
            omega

/-
Prove the following inequality, which is somewhat easier.
Remember, if you do a proof by induction as in the previous theorem,
you have to delete the `:= by`.
-/

@[exercise "2a" 5]
theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t := by
  sorry

/-
Define the `flip` operation on binary trees, which recursively swaps the
left and right subtrees. For example, it should map the tree on the
left to the one on the right:

       .          .
      / \        / \
     .   .      .   .
      \            /
       .          .


-/

def flip : BinTree → BinTree := sorry

/-
If you did it right, the proof of the following should be `rfl`.
-/

@[exercise "2b" 5]
theorem ex2b: flip (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := sorry

/-
Also prove the following:
-/

@[exercise "2c" 5]
theorem size_flip : ∀ t, size (flip t) = size t := sorry

end BinTree


/-
EXERCISE 3. Structural induction on formulas.
-/

inductive PropForm : Type where
  | var (n : ℕ)           : PropForm
  | fls                   : PropForm
  | conj (A B : PropForm) : PropForm
  | disj (A B : PropForm) : PropForm
  | impl (A B : PropForm) : PropForm

namespace PropForm

/-
This defines what it means to evaluate a propositional formula, given an
assignment of truth values.
-/

def eval : PropForm → (ℕ → Bool) → Bool
  | var n,    v => v n
  | fls,      _ => false
  | conj A B, v => A.eval v && B.eval v
  | disj A B, v => A.eval v || B.eval v
  | impl A B, v => ! A.eval v || B.eval v

/-
This defines what it means to substitute a formula for a variable.
-/

def subst : PropForm → ℕ → PropForm → PropForm
  | var n,    m, C => if n = m then C else var n
  | fls,      _, _ => fls
  | conj A B, m, C => conj (A.subst m C) (B.subst m C)
  | disj A B, m, C => disj (A.subst m C) (B.subst m C)
  | impl A B, m, C => impl (A.subst m C) (B.subst m C)

/-
The next definition and theorem are examples. I will discuss them
in class.

Note that in the compound cases, we use the inductive hypotheses
for the constituent formulas.

The `split` tactic splits theorems involving if-then-else into
two cases.
-/

def free_variables : PropForm → Finset ℕ
  | var n    => {n}
  | fls      => ∅
  | conj A B => A.free_variables ∪ B.free_variables
  | disj A B => A.free_variables ∪ B.free_variables
  | impl A B => A.free_variables ∪ B.free_variables

theorem subst_eq_of_not_mem_free_variables :
    ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.free_variables →
      A.subst n C = A
  | var m, n, C, h => by
      rw [subst]
      split_ifs with h0
      . simp [h0, free_variables] at h
      rfl
  | fls, n, C, _ => by rw [subst]
  | conj A B, n, C, h => by
      rw [subst, subst_eq_of_not_mem_free_variables A,
            subst_eq_of_not_mem_free_variables B] <;>
      simp [free_variables] at h <;> tauto
  | disj A B, n, C, h => by
      rw [subst, subst_eq_of_not_mem_free_variables A,
            subst_eq_of_not_mem_free_variables B] <;>
      simp [free_variables] at h <;> tauto
  | impl A B, n, C, h => by
      rw [subst, subst_eq_of_not_mem_free_variables A,
            subst_eq_of_not_mem_free_variables B] <;>
      simp [free_variables] at h <;> tauto

/-
See if you can make sense of the following theorem on paper, and prove it.
The simplifier will do almost all the work for you; in the base case,
you will have to use the `split` tactic.
-/

@[exercise "3" 5]
theorem subst_eval_eq : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool),
    (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m)
  | var m, n, C, v => by
      sorry
  | fls, n, C, v => by
      sorry
  | conj A B, n, C, v => by
      sorry
  | disj A B, n, C, v => by
      sorry
  | impl A B, n, C, v => by
      sorry

end PropForm
