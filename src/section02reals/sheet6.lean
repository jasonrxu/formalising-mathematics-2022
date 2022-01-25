/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet5 -- import a bunch of previous stuff

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in a solutions video,
so if you like you can try some of them and then watch me
solving them.

Good luck! 
-/


/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsto_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : tendsto a t) :
  tendsto (λ n, 37 * a n) (37 * t) :=
begin
  unfold tendsto,
  intros,
  have : ε / 37 > 0, linarith,
  specialize h (ε / 37) this,
  cases h with b hb,
  use b,
  intros n hbn,
  specialize hb n hbn,
  rw ←(mul_sub 37 (a n) t),
  rw abs_mul 37 (a n - t),
  have : 0 ≤ (37 : ℝ), linarith,
  rw abs_eq_self.2 this,
  linarith,
end

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : 0 < c) : tendsto (λ n, c * a n) (c * t) :=
begin
  unfold tendsto,
  intros,
  have : ε / c > 0, exact div_pos H hc,
  specialize h (ε / c) this,
  cases h with b hb,
  use b,
  intros n hbn,
  specialize hb n hbn,
  rw ←(mul_sub c (a n) t),
  rw abs_mul c (a n - t),
  rw abs_eq_self.2 (le_of_lt hc),
  exact (lt_div_iff' hc).mp hb,
end

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : c < 0) : tendsto (λ n, c * a n) (c * t) :=
begin
  have hneg := tendsto_neg h,
  have hcneg : 0 < -c, linarith,
  have h := tendsto_pos_const_mul hneg hcneg,
  dsimp at h,
  rw ←neg_mul_neg c t,
  have hh : (λ n : ℕ, -c * -a n) = λ n : ℕ, c * a n := funext (λn, neg_mul_neg c (a n)),
  rw ←hh,
  assumption,
end

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsto_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, c * a n) (c * t) :=
begin
  cases lt_or_ge 0 c with hc hc,
  exact tendsto_pos_const_mul h hc,
  cases eq_or_lt_of_le hc with hc hc,
  {
    rw hc,
    norm_num,
    exact tendsto_const 0,
  },
  exact tendsto_neg_const_mul h hc,
end

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsto_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, a n * c) (t * c) :=
begin
  rw mul_comm t c,
  rw (funext (λn, mul_comm (a n) c) : (λ n : ℕ, a n * c) = λ n : ℕ, c * a n),
  exact tendsto_const_mul c h
end

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tendsto_neg' {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  convert tendsto_const_mul (-1) ha, -- read about `convert` on the community web pages
  { ext, simp }, -- ext is a generic extensionality tactic. Here it's being
                 -- used to deduce that two functions are the same if they take
                 -- the same values everywhere
  { simp },
end

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsto_of_tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (h1 : tendsto (λ n, a n - b n) t) (h2 : tendsto b u) :
  tendsto a (t+u) :=
begin
  have := tendsto_add h1 h2,
  norm_num at this,
  exact this,
end

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsto_sub_lim {a : ℕ → ℝ} {t : ℝ}
  (h : tendsto a t) : tendsto (λ n, a n - t) 0 :=
begin
  have := tendsto_sub h (tendsto_const t),
  norm_num at this,
  exact this,
end

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsto_zero_mul_tendsto_zero
  {a b : ℕ → ℝ} (ha : tendsto a 0) (hb : tendsto b 0) :
  tendsto (λ n, a n * b n) 0 :=
begin
  unfold tendsto,
  unfold tendsto at ha hb,
  specialize ha 0.5,
  have h_one_half_zero : (1/2 : ℝ) > 0, linarith,
  specialize ha h_one_half_zero,
  cases ha with ba ha,
  intros ε hε,
  specialize hb ε hε,
  cases hb with bb hb,
  use max ba bb,
  intros n hn,
  have : ba ≤ n ∧ bb ≤ n := max_le_iff.mp hn,
  specialize ha n this.1,
  specialize hb n this.2,
  norm_num at ha hb ⊢,
  rw abs_mul (a n) (b n),
  cases eq_or_lt_of_le (abs_nonneg (b n)),
  {
    rw ←h,
    linarith,
  },
  have := mul_lt_mul ha (le_of_lt hb) h (le_of_lt h_one_half_zero),
  linarith,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsto_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : tendsto a t)
  (hb : tendsto b u) : tendsto (λ n, a n * b n) (t * u) :=
begin
  set f := (λ n, (a n * b n) + t * u) with hf,
  suffices h : tendsto f (t * u + t * u),
  {
    have := tendsto_sub h (tendsto_const (t * u)),
    norm_num at this,
    exact this,
  },
  suffices h : tendsto (λ n, a n * b n + t * u - a n * u - t * b n) 0,
  {
    have hanu := tendsto_mul_const u ha,
    have htbn := tendsto_const_mul t hb,
    have := tendsto_add (tendsto_add h htbn) hanu,
    norm_num at this,
    exact this,
  },
  have hat := tendsto_sub_lim ha,
  have hbu := tendsto_sub_lim hb,
  have := tendsto_zero_mul_tendsto_zero hat hbu,
  dsimp at this,
  suffices h : (λ n, (a n - t) * (b n - u)) = (λ n, a n * b n + t * u - a n * u - t * b n),
  {
    rw ←h,
    exact this,
  },
  ext,
  linarith,
end

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsto_unique (a : ℕ → ℝ) (s t : ℝ)
  (hs : tendsto a s) (ht : tendsto a t) : s = t :=
begin
  have h := tendsto_sub hs ht,
  norm_num at h,
  by_cases hst : (s - t = 0),
  linarith,
  specialize h (|s - t| / 2),
  have : |s - t| / 2 > 0,
  {
    suffices : |s - t| > 0, linarith,
    have := abs_nonneg (s - t),
    cases (eq_or_lt_of_le this),
    have := abs_eq_zero.mp (eq.symm h_1),
    contradiction,
    assumption,
  },
  specialize h this,
  cases h with b h,
  specialize h b (le_refl b),
  norm_num at h,
  rw ←(abs_sub_comm s t) at h,
  linarith,
end
