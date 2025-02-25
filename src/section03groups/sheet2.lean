/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import solutions.section03groups.sheet1 -- imports our definition of `mygroup`

/-!

# Challenge sheet

This is an optional "puzzle" sheet, which won't teach you any
new Lean concepts but will give you some practice in rewriteology,
and will teach you pretty much all there is to know about the
question "which axioms of a group can I safely drop?" If you're
not into puzzles like this, just move on to sheet 3.

It turns out that two of the axioms in our definition of a group
are not needed; they can be deduced from the others. Let's define
a "weak group" class, where we only have three of the group axioms.
The question is: can you prove that a weak group is a group?
The last def, `to_mygroup`, does this, but you need to fill in the
sorrys first. Note that the simplifier is less use to you now; we've
trained it to solve problems about `mygroup`s but it doesn't
know anything about `myweakgroup`.

-/

-- removing `mul_one` and `mul_inv_self`
class myweakgroup (G : Type)
  extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)

namespace myweakgroup

variables {G : Type} [myweakgroup G] (a b c : G)

/-

One way of doing it: try proving 

`mul_left_cancel : a * b = a * c → b = c`

and then

`mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c`

first.

-/

lemma mul_left_cancel : a * b = a * c → b = c :=
begin
  intro h,
  have h2 := @eq.subst _ (λ g, a⁻¹ * a * b = a⁻¹ * g) (a * b) (a * c) h,
  dsimp at h2,
  rw inv_mul_self at h2,
  rw ←mul_assoc at h2,
  rw inv_mul_self at h2,
  specialize h2 (by triv),
  rw one_mul at h2,
  rw ←mul_assoc at h2,
  rw inv_mul_self at h2,
  rw one_mul at h2,
  exact h2,
end

lemma mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c :=
begin
  intro h,
  rw ←one_mul b at h,
  rw ←inv_mul_self a at h,
  rw mul_assoc at h,
  exact mul_left_cancel _ _ _ h,
end

lemma mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw inv_mul_self a,
end

example (a : G) : a * 1 = a :=
begin
  have : (1 : G) * 1 = 1, rw one_mul,
  nth_rewrite 0 ←(inv_mul_self a) at this,
  nth_rewrite_rhs 0 ←(inv_mul_self a) at this,
  rw mul_assoc at this,
  have := mul_left_cancel _ _ _ this,
  exact this,
end

lemma mul_inv_self (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

def to_mygroup (G : Type) [myweakgroup G] : mygroup G :=
{ mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  inv_mul_self := inv_mul_self,
  mul_inv_self := mul_inv_self }

end myweakgroup

/-
If you want to take this further: prove that if we make
a new class `my_even_weaker_group` by replacing
`one_mul` by `mul_one` in the definition of `myweakgroup`
then it is no longer true that you can prove `mul_inv_self`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_self` but which really are not groups.
Can you find an example? Try it on paper first. 
-/

-- claim: not a group in general
class my_even_weaker_group (G : Type)
  extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(mul_one : ∀ a : G, a * 1 = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)