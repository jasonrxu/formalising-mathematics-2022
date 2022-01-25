/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false := λf, f (true.intro)

example : false → ¬ true := λx _, x

example : ¬ false → true := λ_, true.intro

example : true → ¬ false := λ_ f, f

example : false → ¬ P := λf _, f

example : P → ¬ P → false := λx f, f x

example : P → ¬ (¬ P) := λx f, f x

example : (P → Q) → (¬ Q → ¬ P) := λpq nq p, nq (pq p)

example : ¬ ¬ false → false := λf, f id

example : ¬ ¬ P → P :=
begin
  intro nnp,
  by_contra h,
  exact (nnp h)
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros hnqnp hp,
  by_contra nq,
  apply hnqnp,
  assumption,
  assumption
end