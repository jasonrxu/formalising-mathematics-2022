/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q := or.inl

example : Q → P ∨ Q := or.inr

example : P ∨ Q → (P → R) → (Q → R) → R := or.elim

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := λh, or.elim h or.inr or.inl

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := or.assoc

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := λhpr hqs hpq, or.elim hpq (or.inl ∘ hpr) (or.inr ∘ hqs)

example : (P → Q) → P ∨ R → Q ∨ R := λhpq hpr, or.elim hpr (or.inl ∘ hpq) or.inr

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
  λhpr hqs, iff.intro (λhpq, or.elim hpq (or.inl ∘ hpr.1) (or.inr ∘ hqs.1))
                      (λhrs, or.elim hrs (or.inl ∘ hpr.2) (or.inr ∘ hqs.2))

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
  iff.intro (λhnpq, and.intro (hnpq ∘ or.inl) (hnpq ∘ or.inr))
            (λhnpnq hpq, or.elim hpq hnpnq.1 hnpnq.2)

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
  iff.intro (λhnpq,
              begin
                by_cases hp : P,
                {
                  right,
                  intro hq,
                  exact (hnpq ⟨hp, hq⟩)
                },
                {
                  left,
                  exact hp
                }
              end)
            (λhnpnq hpq, or.elim hnpnq (λhnp, hnp hpq.1) (λhnq, hnq hpq.2))