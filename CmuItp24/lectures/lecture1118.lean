import CmuItp24.MVarGraph

/-
# Announcements

The final project is due on Friday, December 6, the last day of class.

Don't put work off until the last minute!

Tell us by end of today (Monday, November 18th) what you plan to do.

For the rest of the semester:
  lectures on Monday and Wednesday
  extra office hour on Friday

Office hours for the rest of the semester:

  Monday, 2-3 (Jeremy)
  Tuesday, 3-4 (Wojciech)
  Wednesday, 11-12 (Wojciech)
  Wednesday, 3:30-4:30 (Eric)
  Thursday, 4-5 (Eric)
  Friday, 12-1 (Jeremy)

# Agenda

Today: metaprogramming in Lean
Wednesday: back to foundations
-/

/-!
## What is a (Lean) proof?

At the most basic level, Lean represents proofs as *proof terms*.

Anything can be proven without tactics - with terms only - though it would be a very bad time.
-/

example {P Q : Prop} (p : P) (q : Q) : P ∧ Q := by
  -- show_term
  constructor
  . exact p
  . exact q

-- goes to ↓

example {P Q : Prop} (p : P) (q : Q) : P ∧ Q :=
  And.intro p q -- or equivalently `⟨p, q⟩`

example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  -- show_term
  intro p
  apply qr
  -- or, with the same effect
  -- refine qr ?q
  apply pq
  exact p

-- goes to ↓

example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R :=
  fun p => qr (pq p)

example {α : Type} {P : α → Prop} {a b c : α} (ab : a = b) (bc : b = c) (pa : P a) : P c := by
  -- show_term
  rw [← bc]
  rw [← ab]
  exact pa

-- goes to ↓

example {α : Type} {P : α → Prop} {a b c : α} (ab : a = b) (bc : b = c) (pa : P a) : P c :=
  -- `Eq.mpr` is a proof term that records as single rewrite
  Eq.mpr (id (congrArg (fun _a => P _a) (Eq.symm bc)))
    (Eq.mpr (id (congrArg (fun _a => P _a) (Eq.symm ab))) pa)

/-!
## Metavariable trees

A *metavariable* (`MVar`) is (more or less) a variable that ranges over Lean terms
(proof terms such as `And.intro p q`, and terms such as `13 + 37`.)

Tactics use metavariables to represent partially finished proof terms.

(Let's see this in analog form first.)
-/

-- Display graph of metavariables.
show_panel_widgets [local CmuItp24.MVarGraph]

-- When printing an assigned metavariable `?m := v`,
-- print out the metavariable name `?m` rather than `v`.
set_option pp.instantiateMVars false
-- Do the same for delayed assigned metavariables.
set_option pp.mvars.delayed true

example {P Q : Prop} (p : P) (q : Q) : P ∧ Q := by
  constructor
  . exact p
  . exact q

example {P Q R : Prop} (p : P) (q : Q) (r : R) : (P ∧ Q) ∧ R := by
  constructor
  constructor
  -- or, with the same effect
  -- repeat constructor
  . exact p
  . exact q
  . exact r

example {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  intro p
  apply qr
  -- or, with the same effect
  -- refine qr ?q
  apply pq
  exact p

example {α : Type} {P Q : α → Prop} (pq : ∀ x, P x → Q x) (px : ∀ x, P x) : ∀ x, Q x := by
  intro y
  apply pq
  apply px

example {α : Type} {P : α → Prop} {a : α} (pa : P a) : ∃ x, P x := by
  refine ⟨?w, ?h⟩
  -- or, with almost same effect (except goals will be swapped)
  -- constructor
  exact a
  exact pa

example {α : Type} {P : α → Prop} {a b c : α} (ab : a = b) (bc : b = c) (pa : P a) : P c := by
  rw [← bc]
  rw [← ab]
  exact pa

example (n : Nat) : n = 0 ∨ ∃ m, n = m + 1 := by
  induction n -- a big mess
  . exact Or.inl rfl
  . exact Or.inr ⟨_, rfl⟩

/-! ## Our very own tactic -/

open Lean Meta Elab Tactic

/-- Does the same thing as `constructor` when the goal is `?A ∧ ?B`. -/
elab "prove_conj" : tactic => do
  -- Obtain a reference to the main goal.
  let g ← getMainGoal

  -- Create metavariables `?A : Prop` and `?B : Prop`
  -- (`Sort 0 ≡ Prop`).
  let mvarA ← mkFreshExprMVar (mkSort 0)
  let mvarB ← mkFreshExprMVar (mkSort 0)

  -- Create the term `?A ∧ ?B : Prop`.
  let termAB ← mkAppM ``And #[mvarA, mvarB]

  -- *Unify* `?A ∧ ?B ≡ goal type`.
  -- This assigns `?A` and `?B` if successful.
  -- E.g. if the goal type is `True ∧ False`,
  -- this will assign `?A := True` and `?B := False`.
  let isMatch ← isDefEq termAB (← g.getType')
  if !isMatch then
    throwError "goal is not a conjunction"

  -- Create metavariables `?proofA : ?A` and `?proofB : ?B`.
  let mvarProofA ← mkFreshExprMVar mvarA
  let mvarProofB ← mkFreshExprMVar mvarB

  -- Create the term `And.intro ?proofA ?proofB : ?A ∧ ?B`.
  let termProofAB ← mkAppM ``And.intro #[mvarProofA, mvarProofB]

  -- Assign the main goal metavariable `?g := And.intro ?proofA ?proofB`.
  g.assign termProofAB

  -- Set the new goals to be `?proofA` and `?proofB`.
  setGoals [mvarProofA.mvarId!, mvarProofB.mvarId!]

example {P Q : Prop} (p : P) (q : Q) : P ∧ Q := by
  prove_conj
  . exact p
  . exact q
