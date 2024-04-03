/-
Copyright (c) 2024  María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic -- imports all Mathlib tactics

/-!
# Propositional Logic in Lean

`P : Prop` means that `P` is a proposition.
`h : P` means that `h` is a proof that `P` is true.

In the `Tactic state` part of the `Lean infoview` window, after the symbol `⊢` we can see the result
we want to prove. Above that line we find the active hypotheses.

Lean uses the following notation for logic connectives:
* `→` ("implies" -- get it by typing `\r` or `→`)
* `¬` ("not" -- type `\not` or `\n`)
* `∧` ("and" -- type `\and` or `\an`)
* `↔` ("if and only if" -- type `\iff` or `\lr`)
* `∨` ("or" -- type `\or` or `\v`

NOTE: in VSCode, to find out how to write a UNICODE symbol, just hover the cursor over it.

# Tactics
To complete these exercises, we will need to use the following Lean tactics, described in the file
`tactics.lean`. The exercises from the first section can be solved using only `intro`, `exact`,
and `apply`. At the beginning of each new section, I indicate which new tactics are needed.

* `intro`
* `exact`
* `apply`
* `rcases`
* `constructor`
* `left`
* `right`
* `by_contra`
-/

-- `P`, `Q`, `R` and `S` denote propositions.
variable (P Q R S : Prop)

/- Convention: we will use variables starting with `h` (like `hP` or `h1`) to denote proofs or
  hypotheses. -/

/-
## Implication
The `sorry` tactic is used to avoid the error otherwise raised by Lean when we skip the proof of a
result.

In each of the following examples, replace the `sorry` by a proof using the tactics
`intro`, `exact` and `apply`. Recall that indentation is important.
-/

/-- Every proposition follows from itself. -/
example : P → P := by
  sorry

/- NOTE: Lean's convention is that `P → Q → R` means `P → (Q → R)` (that is, implication is
 right-associative).

In particular, in this example we need to show `P → (Q → P)`.

As a general rule, if we don't know whether an operation is right or left associative, we can
check it in the `Tactic state`, by hovering the cursor above the corresponding line.
-/
example : P → Q → P := by
  sorry

/-- "Modus Ponens": given `P` and `P → Q`, show `Q`. -/
lemma modus_ponens : P → (P → Q) → Q := by
  sorry

/-!
# Negation
In Lean, `¬ P` *is defined as* `P → False`. Hence, `¬ P` y `P → False`
are *definitionally equal*.
-/
example : ¬ P ↔ (P → False) := by
  sorry

example : False → ¬ True := by
  sorry

example : P → ¬ P → False := by
  sorry

/-!
# Conjunction
new tactics:
* `rcases`
* `constructor`
-/

example : P ∧ Q → P := by
  sorry

example : P → Q → P ∧ Q := by
  sorry

/-!
# Disjunction
New tactics
* `left` and `right`
* `rcases` (new use case)
-/

example : P → P ∨ Q := by
  sorry


/- `∨` is symmetric. -/
example : P ∨ Q → Q ∨ P := by
  sorry

/-! # Classical Logic
All of the exercises above can be proved constructively. However, in Lean we can also use classical
reasoning.

The tactic `by_cases hP : P` splits the main goal into two cases, assuming `hP : P` in the first
branch, and `hP : ¬ P` in the second branch. That is, we are using the `law of the excluded middle`
(for every proposition `P`, `P ∨ ¬ P` is true).

We can also write proofs by contradiction, using `by_contra h`.

Note also that the tactic `exfalso` can be used to change any goal to `False`.

-/
example : (¬ Q → ¬ P) → (P → Q) := by
  sorry

example : ¬ ¬ P → P := by
  sorry
