/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic

/-!
# New tactics
* `ext`
* `swap`
-/

/- ## ext
To prove that two sets are equal, it is enough to show that they have the same elements.
Given the goal `⊢ S = T`, where `S` and `T` are sets (of elements of the same type), `ext a`
changes the goal to `⊢ a ∈ S ↔ a ∈ T`.
-/

example (X : Type) (S T : Set X) (hST : S ⊆ T) (hTS : T ⊆ S) : S = T := by
  ext a
  constructor
  . apply hST
  . apply hTS

example (X Y : Type) (f : X → Y) : id ∘ f = f := by
  ext x
  rw [Function.comp_apply, id_eq]

/- ## swap
The `swap` tactic exchanges the next two goals.

The related tactic `pick_goal n` moves the `n`th goal to the front.
-/

example {Ω : Type} {X Y : Set Ω} (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := by
  ext a
  constructor
  swap
  . apply hYX
  . apply hXY
