/-
Copyright (c) 2024  María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic -- imports all Mathlib tactics

set_option autoImplicit false

/-!

# Tactics
In this file we describe the behaviour of the following Lean tactics and we give some examples.
* `sorry`
* `intro`
* `exact`
* `apply`
* `rcases`
* `constructor`
* `left`
* `right`
* `by_contra`
* `by_cases`

TIP: Take advantage of Lean's interactive features. Inside a proof in tactic mode (starting with
`by`), by clicking at the end of each line, we can see in the `Lean infoview` window the current
state of our proof.
-/

/- # Tactics -/

--  `P`, `Q` and `R` denote propositions.
variable (P Q R : Prop)

/- ## sorry
  `sorry` closes any goal and gives raise to a warning which appears in the "All Messages" section
  of the "Lean infoview". At the bottom of the screen, we can see the total number of warnings.
-/

theorem fermats_last_theorem : ∀ (x y z : ℤ), ∀ n ≥ 3, x^n + y^n = z^n → x*y*z = 0 := by sorry

/- ## exact
If our goal is to prove `P` and we have the hypothesis `hP : P` available, we can close the goal by
using `exact hP`.

NOTE: `exact P` does not work (we should not confuse the proposition `P` with its proof `hP`).  -/

example (hP : P) (_hQ : Q) : P := by
  exact hP

/-  ## intro

Given the goal `P → Q`, the tactic `intro hP` introduces a local hypothesis `hP : P` and replaces
the goal by `Q`.

VARIANT: `intro` can also be used to introduce several variables at the same time. -/

example (hQ : Q) : P → Q := by
  intro _hP
  exact hQ

example : Q → P → Q := by
  intro hQ _hP
  exact hQ


/- ## apply

The `apply` tactic can be use to reason backwards. For example, given the tactic state

hPQ : P → Q
⊢ Q,

the effect of `apply hPQ` will be to change it to

hPQ : P → Q
⊢ P.

That is, proving `Q` gets reduced to proving `P`, and the active hypotheses do not change.

In general, `apply h` tries to unify the current goal with the conclusion of the term `h`. If it
succeeds, the goal is replaced by one or several goals (as many as the number of premises of `h`).
-/

example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP


-- In this example, `apply` generates two subgoals
example (hP : P) (hQ : Q) (h : P → Q → Q)  : Q := by
  apply h
  /- STYLE RECOMMENDATION: when the application of a goal introduces several new subgoals, it is
    recommended to use a dot `.` before the proof of each of the goals.
    The dots are optional, but they serve to focus the goal: within the block introduced by the dot,
    only one goal is visible, and it must be completed before the end of the block -/
  . exact hP
  . exact hQ


/- ## rcases

`rcases` is a general purporse tactic to deconstruct hypotheses. Here we present two of the most
basic use cases.


### Examples

1) Given the hypothesis `hPaQ : P ∧ Q`, the instruction `rcases hPaQ with ⟨hP, hQ⟩` will delete
`hPaQ` and replace it by the two hypotheses
```
hP : P
hQ : Q
```

2) Given the hypothesis `hPiQ : P ↔ Q`, `rcases hPiQ with ⟨hP, hQ⟩` will replace `hPiQ` by the
two hypotheses
```
hPQ : P → Q
hQP : Q → P
```

On the other hand, we will later see that the tactic `rw` can also be used with hypotheses of the
form  `h : P ↔ Q`, and we will need to figure out which tactic is more useful in each case.


3) Given the hypothesis `hPQ : P ∨ Q`, `rcases hPQ with (hP | hQ)`  divides the proof of the goal
in two cases: one assuming `hP : P` and one assuming `hQ : Q`.
-/


/- ## constructor

If the current goal is a conjunction `⊢ P ∧ Q`, we can used the tactic `constructor` to replace it
by the two goals `⊢ P` and `⊢ Q`.

After using `constructor`, the style recommendation is to use a dot to indicate the start of the
proof of each of the new goals.

```
constructor
. proof of P
. proof of Q
```

Similarly, `constructor` transforms the goal `⊢ P ↔ Q` in two goals `⊢ P → Q` and `⊢ Q → P`.

-/

/- ## left

The tactic `left` replaces the goal `⊢ P ∨ Q` by `⊢ P`. -/

example (hP : P) : P ∨ Q := by
  left
  exact hP

/- ## right

The tactic `right` replaces the goal `⊢ P ∨ Q` by `⊢ Q`. -/

example (hQ : Q) : P ∨ Q := by
  right
  exact hQ

/- ## by_contra
The tactic `by_contra` allows us to write proofs by contradiction. Given the goal
```
⊢ P
```

the instruction `by_contra h` will change the "Tactic state" to

```
h : ¬P
⊢ false
```

-/

/-## by_cases

Given a proposition `P`, the tactic `by_cases h : P` divides the proof of the goal in two cases:
one assuming `h : P` and one assuming `h : ¬P`.
-/

example : P ∨ ¬ P := by
  by_cases hP : P
  . left
    exact hP
  . right
    exact hP
