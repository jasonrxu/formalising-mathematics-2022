/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

/-!

# Doing algebra in the real numbers

The `ring` tactic will prove algebraic identities like
(x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2. See if you can use
it to prove these theorems.

## New tactics you will need

* `ring`
* `intro` (new functionality)

-/

example (x y : ℝ) : (x + y) ^ 2  = x ^ 2 + 2 * x * y + y ^ 2 :=
begin
  sorry
end

example : ∀ (a b : ℝ), ∃ x, 
  (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 :=
begin
  sorry,
end

example : ∃ (x : ℝ), ∀ y, y + y = x * y :=
begin
  sorry
end

example : ∀ (x : ℝ), ∃ y, x + y = 2 :=
begin
  sorry
end

example : ∀ (x : ℝ), ∃ y, x + y ≠ 2 :=
begin
  sorry,
end

