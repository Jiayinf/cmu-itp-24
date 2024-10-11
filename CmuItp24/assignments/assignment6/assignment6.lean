import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import CmuItp24.Autograde

/-
EXERCISE 1. Using the definition `mypow a n`, which is supposed to define
exponentiation `a^n`, use induction to prove the theorem below.
-/

section
variable {α : Type*} [CommMonoid α]

def mypow : α → ℕ → α
  | a, 0       => 1
  | a, (n + 1) => a * (mypow a n)

#eval mypow 3 5

theorem mypow_zero (a : α) : mypow a 0 = 1 := rfl

theorem mypow_succ (a : α) (n : ℕ) : mypow a (n + 1) = a * mypow a n := rfl

@[exercise "1" 4]
theorem mypow_add (a : α) (m n : ℕ) : mypow a (m + n) = mypow a m * mypow a n := by
  induction' m with m ih
  . simp [mypow_zero, Nat.zero_add]
  . rw [mypow_succ, mul_assoc]
    rw [←ih]
    rw [←mypow_succ]
    rw [add_assoc]
    rw [add_comm 1 n]
    rw [add_assoc]

end

/-
EXERCISE 2.

In class, we have used ordinary induction on the natural numbers,
which allows you to prove `p n` for an arbitrary natural number
`n` by proving `p 0` and `∀ m, p m → p m.succ`.

It is often more useful to the principle of *complete induction*
or *strong induction*. This is found in the library under the
name `nat.strong_induction_on`, but the exercise below asks you
to prove it independently, using ordinary induction on the natural numbers.
The principle is stated in a form that the induction tactic
can use it, as illustrated in exercise 3.

The trick is to prove the stronger claim `∀ n, ∀ m < n, p m` by
induction on the natural numbers. The `suffices` step in the proof
show that this suffices to establish `p n` for the *particular* `n` in
the context. Once we have done that, we throw away the particular `n`,
and focus on proving the stronger claim by induction.
-/

section

@[exercise "2" 7]
theorem complete_induction_on {P : ℕ → Prop} (n : ℕ)
    (h : ∀ n, (∀ m < n, P m) → P n) : P n := by
  suffices h' : ∀ n, ∀ m < n, P m by
    exact h n (h' n)
  clear n
  intro n
  induction' n with n ih
  · intros m hlt
    exfalso  -- There can't be any `m` such that `m < 0`.
    exact Nat.not_lt_zero m hlt
  . intros m hlt
    cases Nat.lt_succ_iff_lt_or_eq.mp hlt with
    | inl hmn =>
      -- Case 1: If m < n, we apply the inductive hypothesis.
      exact ih m hmn
    | inr hmeq =>
      -- Case 2: If m = n, we apply the hypothesis `h` for `n.succ`.
      rw [hmeq]
      exact h n (ih)

end

/-
EXERCISE 3.

In this exercise, we use the principle of strong induction to show that
every natural number greater than or equal to two has a prime divisor.

You can use the lemma `exists_lt_dvd_of_not_prime`. After the boilerplate
that we have set up for you, you should formalize the following argument:
if `n` is prime, we are done.  If `n` is not prime, the lemma tells us that
there it has a nontrivial divisor `m < n`, and we can apply the induction
hypothesis to that.

Remember that you can use `by_cases h : Nat.Prime n` to split into cases
where `n` is prime or not.
-/

-- This follows straightforwardly from the definition of `Nat.Prime`.
theorem exists_lt_dvd_of_not_prime {n : Nat} (h : ¬ Nat.Prime n) (h' : 2 ≤ n) :
  ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n := by
  simp [Nat.prime_def_lt'] at h
  exact h h'

@[exercise "3" 7]
theorem exists_prime_dvd : ∀ n, 2 ≤ n → ∃ p, Nat.Prime p ∧ p ∣ n := by
  intro n
  induction' n using complete_induction_on with n ih
  intro nle
  by_cases hprime : Nat.Prime n
  · exact ⟨n, hprime, dvd_rfl⟩
  · obtain ⟨m, hm_le, hm_lt, hmdvd⟩ := exists_lt_dvd_of_not_prime hprime nle
    have := ih m hm_lt hm_le
    obtain ⟨p, hprime_p, hpdvdm⟩ := this
    exact ⟨p, hprime_p, dvd_trans hpdvdm hmdvd⟩

/-
EXERCISE 4.

Finally, in this exercise, we define the structure of a `Quasigroup`,
show that the integers with subtraction form an instance, and prove
some basic properties.

You can find the definition of a quasigroup here:

  https://en.wikipedia.org/wiki/Quasigroup

We'll use the notation `ldiv a b` for left division (on Wikipedia, `a \ b`),
and we'll use `rdiv a b` for right division (on Wikipedia, `a / b`).

(Instantiating the integers as a quasigroup is dangerous, because it
redefines the notation of multiplication to mean subtraction. But what
happens in 21-321 stays in 21-321.)
-/

/-
First, fill in the remaining axioms. E.g. the first should say,
"for any `a`, `b` and `x`, if `x` satisfies the defining axiom for `ldiv a b`
(that is, the cancellation law), then it is equal to `ldiv a b`."
-/

@[exercise "4a" 4]
class Quasigroup (α : Type*) extends Mul α where
  ldiv : α → α → α
  rdiv : α → α → α
  mul_ldiv_cancel : ∀ a b, a * ldiv a b = b
  rdiv_mul_cancel : ∀ a b, rdiv a b * b = a
  ldiv_unique : ∀ a b x, a * x = b → x = ldiv a b
  rdiv_unique : ∀ a b x, x * b = a → x = rdiv a b

/-
Declaring `Quasigroup` as a `class` means
that you can use the constants and axioms
without explicitly referring to a particular instance of `Quasigroup`.
-/

section
open Quasigroup

example {α : Type*} [Quasigroup α] (c d : α) : c * ldiv c d = d := by
  apply mul_ldiv_cancel

example {α : Type*} [Quasigroup α] (c d e : α) :
    c * ldiv c d * e = d * e := by
  rw [mul_ldiv_cancel]

end

/-
Next, show that the integers with subtraction are an instance. You will
have to figure out the right definitions of `ldiv` and `rdiv`. For
example, if you decide `ldiv a b` should be `a * b`, write
`ldiv := fun a b => a * b`.

Note that in goals within the instance definition, you might see "multiplication"
which is really integer subtraction, because that's we defined it as! To check
which one it really is, you can click on the `*` operation in the infoview and look
for something like `{mul := int.sub}`.

Also, the `show` tactic can sometimes be used to unfold definitions. For example
on the goal `⊢ a * b = stuff`, `show a - b = stuff` should work.
-/

@[exercise "4b" 6]
instance : Quasigroup ℤ where
  mul := Int.sub
  ldiv := fun a b => a - b
  rdiv := fun a b => a + b
  mul_ldiv_cancel := by
    intros a b
    show a - (a - b) = b
    rw [Int.sub_sub_self]
  rdiv_mul_cancel := by
    intros a b
    show (a + b) - b = a
    rw [Int.add_sub_cancel]
  ldiv_unique := by
    intros a b x h
    show x = a - b
    rw [←h]
    show x = a - (a - x)
    rw [Int.sub_sub_self]
  rdiv_unique := by
    intros a b x h
    show x = a + b
    rw [←h]
    show x = x - b + b
    rw [Int.sub_add_cancel]

/- Finally, prove that some identities hold in *any* quasigroup. -/

namespace Quasigroup
variables {α : Type*} [Quasigroup α]

@[exercise "4c" 2]
theorem eq_ldiv_mul_self (y x : α) : y = ldiv x (x * y) := by
  -- have h : x * ldiv x (x * y) = x * y := mul_ldiv_cancel x (x * y)
  apply ldiv_unique
  rfl



@[exercise "4d" 2]
theorem eq_mul_rdiv_self (y x : α) : y = rdiv (y * x) x := by
  apply rdiv_unique
  rfl

@[exercise "4e" 4]
theorem left_cancel (a b c : α) (h : a * b = a * c) : b = c := by
  have hb : b = ldiv a (a * b) := ldiv_unique a (a * b) b rfl
  have hc : c = ldiv a (a * c) := ldiv_unique a (a * c) c rfl
  have hk : b = ldiv a (a * c) := by
    rw [hb, h]
  have hr : b = c := by
    rw [hk,  ←hc]
  apply hr

@[exercise "4f" 4]
theorem right_cancel (a b c : α) (h : a * b = c * b) : a = c := by
  have ha : a = rdiv (a * b) b := rdiv_unique (a * b) b a rfl
  have hc : c = rdiv (c * b) b := rdiv_unique (c * b) b c rfl
  have hk : a = rdiv (c * b) b := by
    rw [ha, h]
  have hr : a = c := by
    rw [hk, ←hc]
  apply hr

end Quasigroup
