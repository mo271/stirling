import tactic
import analysis.special_functions.log
import analysis.special_functions.log_deriv
import data.fintype.basic
import algebra.big_operators.basic
import algebra.big_operators.intervals
import data.finset.sum
import data.real.basic
import topology.instances.real
import topology.instances.ennreal
import order.filter
import order.bounded_order
import analysis.special_functions.pow

import part0

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat


-- part 1 of https://proofwiki.org/wiki/Stirling%27s_Formula
-- first section of part 1


--uses an,
lemma tendsto_succ (an : ℕ → ℝ) (a:ℝ): tendsto an at_top (𝓝 a) ↔
tendsto (λ n : ℕ, (an n.succ)) at_top (𝓝 a) :=
begin
  split,
  {
    intro h,
    -- rw tendsto at h,
    rw tendsto_at_top' at h,
    rw tendsto_at_top',
    intros,
    have g := h s H,
    cases g with m gm,
    use m,
    intro b,
    intro hb,
    have hbsucc: b.succ >= m := le_succ_of_le hb,
    exact gm b.succ hbsucc,
  },
  { intro h,
    -- rw tendsto at h,
    rw tendsto_at_top' at h,
    rw tendsto_at_top',
    intros,
    have g := h s H,
    cases g with m gm,
    use m.succ,
    intro b,
    intro hb,
    cases b,
    exfalso,
    exact not_succ_le_zero m hb,
    have hbm: b >= m := succ_le_succ_iff.mp hb,
    exact gm b hbm,
  },
end


noncomputable def an (n : ℕ) : ℝ  := (n.factorial :ℝ )
/ ((real.sqrt(2*(n))*((n/(exp 1)))^n))

noncomputable def term (x : ℝ)(n : ℕ) : ℝ :=
   ((-1)*((-x)^(n + 1) / ((n : ℝ) + 1)) + (x^(n + 1)/((n:ℝ) + 1)))

lemma term_def  (x: ℝ) : term x =(λ n,  ((-1)*((-x)^(n + 1) / ((n : ℝ) + 1)) + (x^(n + 1)/((n:ℝ) + 1)))) :=
by refl


--uses term,
lemma log_sum_plus_minus (x : ℝ) (hx: |x| < 1) : has_sum (λ k:ℕ,
(2:ℝ)*(1/(2*↑k + 1))*(x^(2* k + 1))) (log (1 + x) - log(1 - x)):=
begin
  have min_one_not_zero : (-1 : ℝ) ≠ ( 0 : ℝ), by linarith,
  have h_min_one_ne_one:  (-1 : ℝ) ≠ ( 1 : ℝ), by linarith,

  have h₁, from has_sum_pow_div_log_of_abs_lt_1 hx,
  have h₂', from has_sum_pow_div_log_of_abs_lt_1 (eq.trans_lt (abs_neg x) hx),
  replace h₂ :=  (has_sum_mul_left_iff min_one_not_zero).mp h₂',
  rw [neg_one_mul, neg_neg, sub_neg_eq_add 1 x] at h₂,
  have h₃, from has_sum.add h₂ h₁,
  rw [tactic.ring.add_neg_eq_sub, ←term_def x ] at h₃,

  let g := (λ (n : ℕ),  (2 * n)),
  rw ←function.injective.has_sum_iff (nat.mul_right_injective two_pos) _ at h₃,

  suffices h_term_eq_goal : (term x ∘ g) = (λ k : ℕ, 2*(1 / (2 * (k : ℝ) + 1)) * x^(2 * k  + 1)),
  begin
    rw h_term_eq_goal at h₃,
    exact h₃,
  end,

  apply funext,
  intro n,

  rw [function.comp_app],
  simp only [g, term],
  rw odd.neg_pow (⟨n, rfl⟩ :odd (2 * n + 1)) x,
  rw [neg_one_mul, neg_div, neg_neg, cast_mul, cast_two],
  ring_nf,

  intros m hm,
  simp only [range_two_mul, set.mem_set_of_eq] at hm,
  simp only [term],
  rw [even.neg_pow (even_succ.mpr hm), succ_eq_add_one],
  ring_nf,
end

--uses nothing?
lemma aux_log (n : ℕ) (hn: n ≠ 0):
log (n.succ/n) = log (1 + 1 / (2*n + 1)) - log (1 - 1/(2*n +1)):=
begin
  have h₁: (2:ℝ)*n + 1 ≠ 0 :=
  begin
    norm_cast,
    exact succ_ne_zero (2*n),
  end,
  have h₂: (2:ℝ)*n + 1 = (2:ℝ)*n + 1 := by refl,
  calc log (n.succ/n) = log(n.succ) - log(n) :
    log_div (cast_ne_zero.mpr (succ_ne_zero n)) (cast_ne_zero.mpr hn)
  ... = log(n.succ) - log(n) +  log 2 - log 2: by simp only [add_tsub_cancel_right]
  ... = log 2 + log(n.succ) - (log 2 + log n): by linarith
  ... = log 2 + log(n.succ) - log(2*n) :
    by rw log_mul (two_ne_zero) (cast_ne_zero.mpr hn)
  ... = log(2 * n.succ) - log(2*n) :
    by rw log_mul (two_ne_zero) (cast_ne_zero.mpr (succ_ne_zero n))
  ... = log(2*n.succ) - log(2*n) - log (2*n + 1) + log (2*n + 1) : by simp only [sub_add_cancel]
  ... = log(2*n.succ) - log (2*n + 1) - (log (2*n) - log (2*n + 1)) : by linarith
  ... = log ((2*n.succ)/(2*n + 1))  - (log (2*n) - log (2*n + 1))  :
    begin
      rw log_div,
      simp only [cast_succ, ne.def, mul_eq_zero, bit0_eq_zero, one_ne_zero, false_or],
      exact cast_ne_zero.mpr (succ_ne_zero n),
      norm_cast,
      exact succ_ne_zero (2*n),
    end
  ... =  log ((2*n.succ)/(2*n + 1))  - log ((2*n)/(2*n + 1)) :
    begin
      rw ←log_div,
      simp only [ne.def, mul_eq_zero, bit0_eq_zero, one_ne_zero,
      cast_eq_zero, false_or],
      exact hn,
      norm_cast,
      exact succ_ne_zero (2*n),
    end
  ... = log(((2*n + 1) + 1)/(2*n + 1)) - log ((2*n)/(2*n + 1)) :
  begin
     have h: (2 : ℝ)*n.succ =  2*n + 1 + 1 :=
      begin
      rw succ_eq_add_one,
      norm_cast,
      end,
    rw h,
  end
  ... = log(((2*n + 1) + 1)/(2*n + 1)) - log ((2*n + 1 - 1)/(2*n + 1)) :
    by simp only [add_sub_cancel]
  ... = log (1 + 1 / (2*n + 1)) - log ((2*n + 1 - 1)/(2*n + 1))  : _
  ... = log (1 + 1 / (2*n + 1)) - log (1 - 1/(2*n +1)) : _,
  rw add_div _ (1 : ℝ),
  rw (div_eq_one_iff_eq h₁).mpr h₂,
  rw sub_div _ (1 : ℝ),
  rw (div_eq_one_iff_eq h₁).mpr h₂,
end

--uses aux_log, log_sum_plus_minus
lemma power_series_ln (n : ℕ) (hn: 0 < n): has_sum
(λ (k : ℕ),
(2:ℝ) * (1/(2*(k : ℝ) + 1))*((1/(2*(n:ℝ) + 1))^(2*k + 1)))
(log (↑n.succ / ↑n)) :=
 begin
  have h₀: 0 <  (2 * n +1) := by exact succ_pos',
  have h₁: |1 / (2 * (n : ℝ) + 1)| < 1 :=
  begin
    norm_cast,
    rw abs_of_pos,
    rw div_lt_one,
    norm_cast,
    rw add_comm,
    apply lt_add_of_zero_lt_left,
    simp only [canonically_ordered_comm_semiring.mul_pos, succ_pos', true_and, hn],
    norm_cast,
    exact h₀,
    simp only [cast_add, cast_mul, cast_bit0, cast_one, one_div, inv_pos],
    norm_cast,
    exact h₀,
  end,
  rw aux_log,
  exact log_sum_plus_minus (1/(2*(n : ℝ)+1)) h₁,

  exact ne_of_gt hn,
 end

noncomputable def bn (n : ℕ) : ℝ := log (an n)

--uses nothing
lemma zero_lt_sqrt_two_n (n : ℕ) : (n ≠ 0) → 0 < real.sqrt (2 * ↑n)  :=
begin
  intro hn,
  apply real.sqrt_pos.mpr,
  norm_cast,
  have hn : 0<n, from zero_lt_iff.mpr hn,
  apply mul_pos two_pos ,
  assumption,
  exact nat.nontrivial,
end

--uses nothing
lemma n_div_exp1_pow_gt_zero(n : ℕ) :  (↑n / exp 1) ^ n >0 :=
begin
  cases n,
  rw pow_zero,
  exact one_pos,
  have hsucc : n.succ > 0, from nat.succ_pos n,
  apply gt_iff_lt.mpr,

  apply pow_pos  _ n.succ,
  apply div_pos_iff.mpr,
  left, split,
  norm_cast, rw ←gt_iff_lt,
  exact hsucc,
  exact (1:ℝ).exp_pos,
end

--uses bn, n_div_exp1_pow_gt_zero, zero_lt_zwrt_two_n
lemma bn_formula (n : ℕ):  bn n.succ = (log ↑n.succ.factorial) -
1/(2:ℝ)*(log (2*↑n.succ)) - ↑n.succ*log (↑n.succ/(exp 1)) :=
begin
  have h3, from  (lt_iff_le_and_ne.mp (zero_lt_sqrt_two_n n.succ (succ_ne_zero n))),
  have h4, from  (lt_iff_le_and_ne.mp (n_div_exp1_pow_gt_zero n.succ )),
  rw [bn, an, log_div, log_mul, sqrt_eq_rpow, log_rpow, log_pow],
  ring,
  rw zero_lt_mul_left,
  norm_cast,
  exact succ_pos n,
  exact zero_lt_two,
  exact h3.right.symm,
  exact h4.right.symm,
  norm_cast,
  exact n.succ.factorial_ne_zero,
  apply (mul_ne_zero h3.right.symm h4.right.symm),
end
