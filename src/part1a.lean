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

lemma tendsto_succ (an : ℕ → ℝ) (a : ℝ) : tendsto an at_top (𝓝 a) ↔
  tendsto (λ n : ℕ, (an n.succ)) at_top (𝓝 a) :=
begin
  have : (λ n : ℕ, (an n.succ))  = an ∘ succ, by refl,
  rw this,
  nth_rewrite_rhs 0 ← tendsto_map'_iff,
  have h : map succ at_top = at_top :=
  begin
    rw map_at_top_eq_of_gc pred 1,
    exact @succ_le_succ,
    intros a b hb,
    cases (exists_eq_succ_of_ne_zero (one_le_iff_ne_zero.mp hb)) with d hd,
    rw [hd, pred_succ],
    exact succ_le_succ_iff,
    intros b hb,
    cases (exists_eq_succ_of_ne_zero (one_le_iff_ne_zero.mp hb)) with d hd,
    rw hd,
    rw pred_succ,
  end,
  rw h,
end

noncomputable def an (n : ℕ) : ℝ := (n.factorial : ℝ) / ((real.sqrt(2 * n) * ((n / (exp 1))) ^ n))

noncomputable def term (x : ℝ) (n : ℕ) : ℝ :=
  ((-1) * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) + (x ^ (n + 1) / ((n : ℝ) + 1)))

lemma term_def (x : ℝ) : term x = (λ n, ((-1) * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) +
  (x ^ (n + 1) / ((n : ℝ) + 1)))) := by refl

--uses term,
lemma log_sum_plus_minus (x : ℝ) (hx: |x| < 1) :
  has_sum (λ k : ℕ, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (x ^ (2 * k + 1))) (log (1 + x) - log(1 - x)) :=
begin
  have min_one_not_zero : (-1 : ℝ) ≠ ( 0 : ℝ), by linarith,
  have h_min_one_ne_one : (-1 : ℝ) ≠ ( 1 : ℝ), by linarith,
  have h₁, from has_sum_pow_div_log_of_abs_lt_1 hx,
  have h₂, from has_sum_pow_div_log_of_abs_lt_1 (eq.trans_lt (abs_neg x) hx),
  replace h₂ :=  (has_sum_mul_left_iff min_one_not_zero).mp h₂,
  rw [neg_one_mul, neg_neg, sub_neg_eq_add 1 x] at h₂,
  have h₃, from has_sum.add h₂ h₁,
  rw [tactic.ring.add_neg_eq_sub, ←term_def x ] at h₃,
  let g := (λ (n : ℕ), (2 * n)),
  rw ← function.injective.has_sum_iff (nat.mul_right_injective two_pos) _ at h₃,
  suffices h_term_eq_goal : (term x ∘ g) = (λ k : ℕ, 2*(1 / (2 * (k : ℝ) + 1)) * x^(2 * k  + 1)),
    by {rw h_term_eq_goal at h₃, exact h₃},
  apply funext,
  intro n,
  rw [function.comp_app],
  simp only [g],
  rw [term],
  rw odd.neg_pow (⟨n, rfl⟩ : odd (2 * n + 1)) x,
  rw [neg_one_mul, neg_div, neg_neg, cast_mul, cast_two],
  ring,
  intros m hm,
  rw [range_two_mul, set.mem_set_of_eq] at hm,
  rw [term, even.neg_pow (even_succ.mpr hm), succ_eq_add_one, neg_one_mul, neg_add_self],
end

--uses nothing?
lemma aux_log (n : ℕ) (hn : n ≠ 0) :
  log (n.succ / n) = log (1 + 1 / (2 * n + 1)) - log (1 - 1 / (2 * n + 1)) :=
begin
  have : (n : ℝ) ≠ 0, from cast_ne_zero.mpr hn,
  have : (2 : ℝ) * n + 1 ≠ 0 :=
  begin
    norm_cast,
    exact (2 * n).succ_ne_zero,
  end,
  rw ← log_div _ _,
  suffices h : (n.succ : ℝ) / (n : ℝ) = (1 + 1 / (2 * n + 1)) / (1 - 1 / (2 * n + 1)),
    from congr_arg log h,
  rw ← one_add,
  all_goals {field_simp},
  ring,
  norm_cast,
  exact succ_ne_zero (2 * n + 1),
end

--uses aux_log, log_sum_plus_minus
lemma power_series_ln (n : ℕ) (hn: 0 < n) : has_sum (λ (k : ℕ),
  (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * ((1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)))
  (log ((n.succ : ℝ) / (n : ℝ))) :=
 begin
  have h₀ : 0 < (((2 * n + 1) : ℕ) : ℝ), from (cast_pos.mpr (2 * n).succ_pos),
  have h₁ : |1 / (2 * (n : ℝ) + 1)| < 1 :=
  begin
    norm_cast,
    rw [abs_of_pos, div_lt_one]; norm_cast,
    any_goals {linarith},
    exact div_pos one_pos h₀,
  end,
  rw aux_log n (ne_of_gt hn),
  exact log_sum_plus_minus (1 / (2 * (n : ℝ) + 1)) h₁,
 end

noncomputable def bn (n : ℕ) : ℝ := log (an n)

--uses nothing
lemma zero_lt_sqrt_two_n (n : ℕ) (hn : n ≠ 0) : 0 < real.sqrt (2 * (n : ℝ)) :=
   real.sqrt_pos.mpr (mul_pos two_pos (cast_pos.mpr (zero_lt_iff.mpr hn)))

--uses nothing
lemma n_div_exp1_pow_gt_zero (n : ℕ) : ((n : ℝ) / exp 1) ^ n > 0 :=
begin
  cases n,
  rw pow_zero,
  exact one_pos,
  exact gt_iff_lt.mpr (pow_pos (div_pos (cast_pos.mpr n.succ_pos ) (exp_pos 1)) (n.succ)),
end

--uses bn, n_div_exp1_pow_gt_zero, zero_lt_zwrt_two_n
lemma bn_formula (n : ℕ): bn n.succ = (log (n.succ.factorial : ℝ)) -
  1 / (2 : ℝ) * (log (2 * (n.succ : ℝ))) - (n.succ : ℝ) * log ((n.succ : ℝ) / (exp 1)) :=
begin
  have h3, from (lt_iff_le_and_ne.mp (zero_lt_sqrt_two_n n.succ (succ_ne_zero n))),
  have h4, from (lt_iff_le_and_ne.mp (n_div_exp1_pow_gt_zero n.succ)),
  rw [bn, an, log_div, log_mul, sqrt_eq_rpow, log_rpow, log_pow],
  linarith,
  rw zero_lt_mul_left,
  exact cast_lt.mpr n.succ_pos,
  exact zero_lt_two,
  exact h3.right.symm,
  exact h4.right.symm,
  exact cast_ne_zero.mpr n.succ.factorial_ne_zero,
  apply (mul_ne_zero h3.right.symm h4.right.symm),
end
