/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Data.Real.Basic -- We import the real numbers.

/-!
Some of these examples are adapted from the talk about structures and classes from LftCM 2022:
<https://icerm.brown.edu/video_archive/?play=2897>
-/

set_option autoImplicit false

/-! # Classes

Reference : Theorem Proving in Lean.

Any structure in Lean can be marked as a *type class*.
We dan declare *class instances*.

When the elaborator is searching for a term of a class, it can check a table with all of the
declared instances to find an appropriate term.
-/


/-! ## Variables -/

-- In Lean, we can use several kinds of variables
variable (r : ℝ) -- explicit variable.
variable {n : ℕ} -- implicit variable. For arguments that can be inferred from others.

example {a : ℕ} (ha : 3 < a) : 3 ≤ a := le_of_lt ha

variable (G : Type)
variable [CommGroup G] -- variables with `[ ]` are inferred by the type class inference system.


/- The variables that we just declared will be visible until the end of the file. If we declare two
variables with the same name (not recommended), Lean will by default use the latter.

We can modify this behaviour by using sections.
-/
section ex

variable (a : ℕ)
variable (a : ℝ) -- in Lean 3, this would have caused an error.
--#check a -- ℝ
--#check a + (1 : ℕ)
--#where

end ex

variable (a : ℕ)

-- Example
lemma Nat.add_pos (n m : ℕ) (hm : 0 < m) :
    0 < n + m := by
  sorry

lemma Nat.add_pos' (n : ℕ) {m : ℕ} (hm : 0 < m) :
    0 < n + m := by
  sorry

example (n m : ℕ) (hm : 0 < m) :
    0 < m + n := by
  rw [add_comm] -- Why does this work?
  sorry
  --exact Nat.add_pos n m hm
  --exact Nat.add_pos n _ hm -- Lean can infer `m` a from hm
  --exact Nat.add_pos' n hm -- with the second variant, the underscore `_` is not needed.

/- Why were we able to use `add_comm` in the previous example?
  `add_comm` is a theorem about additive commutative semigroups.
  Lean automatically found the commutative semigroup structure on `ℕ`, using a process called
  *type class inference*. -/

/- Any structure in Lean can be marked as a *type class* For example,
  `AddGroup` is the class of additive groups. -/
--#check AddGroup
--#print AddGroup

/- We can declare instances of a class. For example, the additive group structure on `ℤ`
is registered as the instance`Int.instAddGroupInt`. -/
--#check Int.instAddGroupInt

/- When the elaborator is searching for a term of a class, it can check a table with the declared
instances to find the appropriate term. -/
--#check add_comm -- has an argument [AddCommSemigroup G]

/- In Lean we use classes to register algebraic, topological, analytic, ..., structures. -/

-- Example: we can create a class to indicate that a type is nonempty.
class MyNonempty (A : Type) : Prop :=
(has_val : ∃ _x : A, true)

instance : MyNonempty ℤ where
  has_val := ⟨0, rfl⟩

instance {A B : Type} [ha : MyNonempty A] [hb : MyNonempty B] :
    MyNonempty (A × B) where
  has_val := by
    cases' ha.has_val with a _
    cases' hb.has_val with b _
    use (a, b)

-- Alternative proof
example {A B : Type} [ha : MyNonempty A] [hb : MyNonempty B] :
    MyNonempty (A × B) := by
  cases' ha.has_val with a _
  cases' hb.has_val with b _
  apply MyNonempty.mk
  use (a, b)

--#where -- Recall that we have [CommGroup G]

-- The following examples are automatically handled by Lean.

example : Group G := by exact CommGroup.toGroup

example : Group G := inferInstance

example : Monoid G := inferInstance

-- Example
instance ProductOfGroups {G H : Type} [Group G] [Group H] : Group (G × H) := inferInstance


-- Example
class R2 :=
(x : ℝ)
(y : ℝ)

instance : Zero R2 where
  zero := sorry

instance : Add R2 where
  add p q := sorry

instance : Neg R2 where
  neg p  := sorry

instance : AddGroup R2 where
  add p q         := p + q
  add_assoc p q r := sorry
  zero            := 0
  zero_add p      := sorry
  add_zero p      := sorry
  neg p           := -p
  add_left_neg    := sorry
  nsmul           := nsmulRec
  zsmul           := zsmulRec
