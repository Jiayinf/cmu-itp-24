import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-
# Announcements

Heather Macbeth is giving a the Michalik Distinguished Lecture at the
University of Pittsburgh  in the Frick Fine Arts Building (room 125) at 3 PM:

  https://www.mathematics.pitt.edu/events/edmund-r-michalik-distinguished-lecture-series-mathematical-sciences-6

She is a leading expert on formalization, and the talk should be really interesting.

The first project will be due on Friday, November 8.

You have to turn in a start on the project on Friday, October 25,
for example, some definitions and a statement of a theorem you
intend to prove. We'll set that up soon.

It won't be graded, but we will ask you to upload it to Gradescope (so we can provide feedback).

# Recap

Last time, I gave an example of a cardinality computation.

# Agenda

Today I'll show you a formalized IMO problem.

Then I'll ask you to introduce yourselves:

- name, year, major
- something about your mathematical interests (e.g. favorite subject, favorite class)
- what you are planning to work on for the first project.

-/

/-
An IMO problem.

It's here:
https://artofproblemsolving.com/wiki/index.php/1965_IMO_Problems/Problem_1

There are more here.
-/

noncomputable section
open Real
open Set

abbrev aux (x : ℝ) := √(1 + sin (2*x)) - √(1 - sin (2*x))

def the_answer := Icc (π/4) (7*π/4)

theorem p1 :
    the_answer = {x ∈ Icc 0 (2*π) | 2 * cos x ≤ |aux x| ∧ |aux x| ≤ √2} := by
  have h0 : ∀ x, (aux x)^2 = 2 - 2*√(cos (2*x)^2) := by
    intro x
    rw [cos_sq', aux, sub_sq, sq_sqrt, sq_sqrt, mul_assoc, ←sqrt_mul]; ring_nf
    repeat { linarith [sin_le_one (2 * x), neg_one_le_sin (2 * x)] }
  have : ∀ x, |aux x| ≤ √2 := by
    intro x
    apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
    simp [aux, ←pow_two, h0]
    positivity
  simp_rw [this, and_true]
  ext x; constructor
  . rw [the_answer]; rintro ⟨h1, h2⟩
    have : x ∈ Ico (π/4) (π / 2) ∪ Icc (π/2) (3*π/2) ∪ Ioc (3*π/2) (7*π/4) := by
      simp [the_answer, mem_Icc, mem_union, mem_Ico, mem_Ioc]
      rcases lt_or_ge x (π/2) with h3 | h3 <;>
        rcases le_or_gt x (3*π/2) with h4 | h4 <;> simp [*]
    rcases this with (⟨_, h2⟩ | ⟨h1, h2⟩) | ⟨h1, _⟩
    . have cos2x_nonpos : cos (2*x) ≤ 0 := by
        apply cos_nonpos_of_pi_div_two_le_of_le <;> linarith
      have cosx_nonneg : 0 ≤ cos x := by
        apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
      have cosx2_nonneg : 0 ≤ 2 * cos x := by linarith
      constructor
      . simp; constructor <;> linarith
      rw [←abs_of_nonneg cosx2_nonneg, ←sq_le_sq, h0, sqrt_sq_eq_abs, abs_of_nonpos cos2x_nonpos,
        cos_two_mul]
      linarith
    . constructor
      . simp; constructor <;> linarith
      trans 0; swap; simp
      suffices cos x ≤ 0 by linarith
      apply cos_nonpos_of_pi_div_two_le_of_le h1
      linarith
    . have cos2x_nonpos : cos (2*x) ≤ 0 := by
        rw [←cos_neg, ←cos_add_two_pi, ←cos_add_two_pi]
        apply cos_nonpos_of_pi_div_two_le_of_le <;> linarith
      have cosx_nonneg : 0 ≤ cos x := by
        rw [←cos_neg, ←cos_add_two_pi]
        apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
      have cosx2_nonneg : 0 ≤ 2 * cos x := by linarith
      constructor
      . simp; constructor <;> linarith
      rw [←abs_of_nonneg cosx2_nonneg, ←sq_le_sq, h0, sqrt_sq_eq_abs, abs_of_nonpos cos2x_nonpos,
        cos_two_mul]
      linarith
  rintro ⟨⟨h1, h2⟩, h3⟩
  by_contra h4
  rw [the_answer, mem_Icc, not_and_or] at h4; push_neg at h4
  have cos2x_nonneg : 0 ≤ cos (2*x) := by
    rcases h4 with h4 | h4
    . apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
    . rw [←cos_sub_two_pi, ←cos_sub_two_pi]
      apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
  have cosx_nonneg : 0 ≤ cos x := by
    rcases h4 with h4 | h4
    . apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
    . rw [←cos_neg, ←cos_add_two_pi]
      apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith
  have cosx2_nonneg : 0 ≤ 2 * cos x := by linarith
  rw [←abs_of_nonneg cosx2_nonneg, ←sq_le_sq, h0, sqrt_sq_eq_abs, abs_of_nonneg cos2x_nonneg,
    cos_two_mul] at h3
  ring_nf at h3
  have : (cos x)^2 ≤ 1/2 := by linarith
  suffices (cos (π/4))^2 < (cos x)^2 by
    rw [cos_pi_div_four, div_pow] at this; norm_num at this
    linarith
  rw [sq_lt_sq, abs_of_nonneg cosx_nonneg, abs_of_nonneg]
  swap; simp [cos_pi_div_four]; positivity
  rcases h4 with h5 | h5
  . apply cos_lt_cos_of_nonneg_of_le_pi_div_two h1 (by linarith) h5
  rw [←cos_neg x, ←cos_add_two_pi (-x)]
  apply cos_lt_cos_of_nonneg_of_le_pi_div_two <;> linarith

end
