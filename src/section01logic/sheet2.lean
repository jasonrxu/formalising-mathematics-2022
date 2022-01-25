/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : true :=
begin
  triv
end

example : true → true := λx, x

example : false → true := λ_, true.intro

example : false → false := λx, x

example : (true → false) → false := λf, f true.intro

example : false → P := false.elim

example : true → false → true → false → true → false := λ_ f _ _ _, f

example : P → ((P → false) → false) := λx f, f x

example : (P → false) → P → Q := λf x, false.elim (f x)

example : (true → false) → P := λf, false.elim (f true.intro)