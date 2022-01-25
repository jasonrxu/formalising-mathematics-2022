/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet3 -- import the definition of `tendsto` from a previous sheet

-- you can maybe do this one now
theorem tendsto_neg {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  unfold tendsto,
  intro,
  intro hε,
  specialize ha ε hε,
  cases ha with b hb,
  use b,
  intros n hbn,
  specialize hb n hbn,
  norm_num,
  rw ←(abs_neg (t - a n)),
  norm_num,
  exact hb,
end

/-
`tendsto_add` is quite a challenge. In a few weeks' time I'll
show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful. 
-/

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsto_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n + b n) (t + u) :=
begin
  intros ε hε,
  unfold tendsto,
  have : ∃ε', ε' = ε / 2, use ε/2,
  cases this with ε' hε',
  unfold tendsto at ha hb,
  have hε'' : ε' > 0, linarith,
  specialize ha ε' hε'',
  specialize hb ε' hε'',
  cases ha with ba ha,
  cases hb with bb hb,
  use (max ba bb),
  intro n,
  specialize ha n,
  specialize hb n,
  intro hm,
  have : ba ≤ n ∧ bb ≤ n, exact (max_le_iff.mp hm),
  specialize ha this.1,
  specialize hb this.2,
  have : |a n - t| + |b n - u| < ε, linarith,
  have : (a n - t) + (b n - u) = a n + b n - (t + u), ring,
  rw ←this,
  have : |(a n - t) + (b n - u)| ≤ |a n - t| + |b n - u|, exact abs_add (a n - t) (b n - u),
  linarith,
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n - b n) (t - u) := tendsto_add ha (tendsto_neg hb)