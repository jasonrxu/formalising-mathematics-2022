/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P := and.left

example : P ∧ Q → Q := and.right

example : (P → Q → R) → (P ∧ Q → R) := λhpqr pq, hpqr pq.1 pq.2

example : P → Q → P ∧ Q := λhp hq, and.intro hp hq

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := λpq, and.intro pq.2 pq.1

example : P → P ∧ true := λhp, and.intro hp true.intro

example : false → P ∧ false := false.elim

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) := λhpq hqr, and.intro hpq.1 hqr.2

example : ((P ∧ Q) → R) → (P → Q → R) := λhpqr hp hq, hpqr (and.intro hp hq)



