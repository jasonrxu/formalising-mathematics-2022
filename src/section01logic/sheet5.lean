/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S X Y : Prop)

example : P ↔ P := iff.intro id id

example : (P ↔ Q) → (Q ↔ P) := λh, iff.intro h.2 h.1

example : (P ↔ Q) ↔ (Q ↔ P) :=
  have f : ∀{X Y}, (X ↔ Y) → (Y ↔ X), from (λ_ _ h, iff.intro h.2 h.1),
  iff.intro f f

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := λhpq hqr, iff.intro (hqr.1 ∘ hpq.1) (hpq.2 ∘ hqr.2)

example : P ∧ Q ↔ Q ∧ P := and.comm

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) := and.assoc

example : P ↔ (P ∧ true) := iff.intro (λh, and.intro h true.intro) (and.left)

example : false ↔ (P ∧ false) := iff.intro (false.elim) and.right

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
  λhpq hrs, iff.intro (λhpr, and.intro (hpq.1 hpr.1) (hrs.1 hpr.2)) (λhqs, and.intro (hpq.2 hqs.1) (hrs.2 hqs.2))

example : ¬ (P ↔ ¬ P) := λ h, have hnp : ¬ P, from λhp, h.1 hp hp, have hp : P, from h.2 hnp, h.1 hp hp
