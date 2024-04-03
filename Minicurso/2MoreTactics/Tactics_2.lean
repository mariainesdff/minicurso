/-
Copyright (c) 2024  María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic -- imports all Mathlib tactics

set_option autoImplicit false

/-!

# Tactics

In this file we describe how to use the tactics:
* `rfl`
* `rw`
* `have`
* `use`
* `intro` (new use case)
* `rcases` (new use case)

-/

/- # Tactics -/

--  `P`, `Q` and `R` denote propositions.
variable (P Q R : Prop)


/- ## rfl
The `rfl` tactic closes goals of the form `⊢ P = Q` where `P` and `Q` are definitionally equal.
It also closes goals of the form `R x y`, where `x` and `y` are definitionally equal, and `R` is a
reflexive binary relation. -/

example : ¬ P ↔ P → False := by
  rfl

/- ## rw

Given an hypothesis `h : P = Q`, we can use `rw [h]` to replace each `P` in the goal by `Q`.
We can also use this tactic when `h` is a logical equivalence instead of an equality.
The argument `h` can be either a local hypothesis or a theorem.

NOTES:

1) If we want to use `h : P = Q` to replace `Q` by `P`, the syntax is `rw [← h]`. We can get the
arrow `←` by typing `\l`.

2) `rw` ONLY works with hypotheses of the form `a = b` or `P ↔ Q`, but not with simple implications
`P → Q` (in that situation, we would use the `apply` tactic).

3) `rw` can be applied to hypotheses, using the keyword `at`.

WARNING: `rw` always invokes the `rfl` tactic.
-/

example (a b : ℕ) (hab : a = b) (hb : b + 1 = 3) : a + 1 = 3 := by
  rw [hab]
  exact hb

example (h1 : P ↔ Q) (h2 : Q → R) : P → R := by
  rw [h1]
  exact h2

example (hQ : ¬ Q) : ¬ (P ∧ Q)  := by
  -- `not_and` is a proof of `¬(P ∧ Q) ↔ (P → ¬Q)`.
  --rw [and_comm]
  rw [not_and]
  intro _
  exact hQ

example (hP : ¬P) (hPQ : P = Q) : ¬ Q := by
  rw [← hPQ]
  exact hP

example (h1 : P ↔ Q) (h2 : P → R) : Q → R := by
  rw [h1] at h2
  exact h2

/- ## have

`have`  is used to add a new hypothesis to the tactic state, which we will need to prove using
the existing hypotheses.

To use this tactic, we write
```
  have h : t := by
    p
```
where `h` is the name of the new hypothesis, `t` is what we want to show, and `p`
is a proof of it.  -/

example : (P → Q) → (¬ Q → ¬ P) := by
  intro hPQ hnQ hP
  have hQ : Q := by -- we introduce the hypothesis, which appears as a new goal in the tactic state
    -- apply hPQ
    --exact hP
    exact hPQ hP -- we prove the new hypothesis
  exact hnQ hQ    -- we use it to prove the main goal


/- ## use
Given a goal `⊢ ∃ a, P a`, where `P a` is a proposition, if `x : X` is the term that we want to use
in the proof, the instruction `use x` will change the goal to `⊢ P x`.
-/

example : ∃ P : Prop, P ∧ True ↔ False := by
  use False
  tauto  -- closes the goal by creating a truth table


/- ## intro (new use case)
If the goal is of the form `∀ x : t, u x`, then `intro x` adds a local hypothesis
`x : t`  and replaces the goal by `⊢ u x`.
 -/

example (X : Type) : ∀ x : X, x = x := by
  intro x
  rfl

/- # A comment about `∀`
Whenever we have an hypothesis of the form `∀ x : t, u x`, we can instantiate it at any
particular term of type `t`.
-/
example (h : ∀ n : ℕ, n < n + 1) : 3 < 4 := by
  exact h 3


/- ## rcases (new use case)
Given a hypothesis `h : ∃ a : X, P a`, where `P a` is a proposition, the tactic
`rcases h with ⟨y, hy⟩` produces a term `x : X` and a proof `hx : P x`.
-/
example (X : Type) (P Q : X → Prop) (h : ∃ x : X, P x) :
  ∃ x : X, P x ∨ Q x := by
  rcases h with ⟨y, hy⟩
  use y
  left
  exact hy
