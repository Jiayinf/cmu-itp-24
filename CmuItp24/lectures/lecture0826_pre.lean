import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-
# Agenda

- Interactive theorem proving
- Course requirements
- Getting set up
- Getting started with Lean

# Introductions

Jeremy Avigad
Wojciech Nawrocki
Eric J. Wang

# Interactive theorem proving

- https://leanprover-community.github.io/
  statistics
  API
- https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/
- https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/

Why?

- verification
- libraries, reference, search
- collaboration
- teaching / learning
- exploring / doing mathematics
- automation and machine learning

# Requirements

This course is unusual:
- Goal: learn to formalize mathematics
- Format: exercises and projects, no exams
- Lectures: in an editor

- Assignments (40%)
- Midterm project (20%)
- Final project (40%)

Workload: standard 9 unit course.

Warnings:
- requires independence
- requires time management / discipline

Information will be posted on Piazza.

Assignments will be submitted on Gradescope.

I will go over the course information sheet.

You will learn to use Lean and Mathlib.

You will use Github to pull assignments and lectures.

Textbook, textbook repostory (can also be used in the cloud)
https://leanprover-community.github.io/mathematics_in_lean/
https://github.com/leanprover-community/mathematics_in_lean

Course repository
https://github.com/avigad/cmu-itp-24/

# Getting set up

I will go over Assignment 1.

To do:
  - Install Git.
  - Install Lean.
  - Fetch Mathematics in Lean.
  - Set up a Git account and get the course repository.
  - Start playing the natural numbers game

The first "real" assignment will be posted on Friday, due the following Friday

# Getting started with Lean

In Lean, there is a single language for:
- defining data types
- defining objects
- stating claims
- writing proofs

Two fundamental facts:
- Everything is an expression.
- Every expression has a type.

Two fundamental operations:
- Check that an expression is well-formed and infer/check its type.
- Evaluate an expression.
-/

#check Nat

#eval 2 + 2

#check 2 + 2 = 4

#check (rfl : 2 + 2 = 4)

def foo := 2

theorem foo_equals_2 : foo = 2 := rfl

/-
More interesting examples:
-/

def f : ℕ → ℕ
  | 0 => 0
  | (n + 1) => (2 * n + 1) + f n


example : Monotone (fun x : ℝ => x + 3) := by
  sorry

example : Monotone (fun x : ℝ => x^3) := by
  sorry
