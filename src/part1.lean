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

--can one do this with is_compl_even_odd or has_sum.even_add_odd?
lemma finset_sum_even_odd  {f : ℕ → ℝ} (n : ℕ):
∑ k in range n, f k =
(∑ l in (range n).filter(odd), f l) +
(∑ m in (range n).filter(even), f m) :=
begin
  have h_union: ∀ ( n : ℕ), range n  =
  (range n).filter(odd) ∪ (range n).filter(even) :=
  begin
    intro n,
    induction n with d hd,
    simp only [range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, empty_union],
    repeat {rw [range_succ]},
    repeat {rw [filter_insert]},

    by_cases h: even d,
      rw [if_pos h, if_neg (even_iff_not_odd.mp h)],
      rw union_insert,
      exact congr_arg (insert d) hd,
    rw [if_neg h, if_pos (odd_iff_not_even.mpr h)],
    rw insert_union,
    exact congr_arg (insert d) hd,
  end,
  nth_rewrite 0 h_union,
  have h_disjoint: ∀ (n : ℕ), disjoint  ((range n).filter(odd))
     ((range n).filter(even)) :=
  begin
    intro n,
    induction n with d hd,
    simp only [range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, disjoint_empty_right],
    repeat {rw range_succ},
    repeat {rw filter_insert},
    by_cases h: even d,
      rw [if_pos h, if_neg (even_iff_not_odd.mp h)],
      rw disjoint_insert_right,
      split,
        rw [mem_filter, not_and],
        intro h₂,
        exact absurd h₂ not_mem_range_self,
      assumption,
    rw [if_neg h, if_pos (odd_iff_not_even.mpr h)],
      rw disjoint_insert_left,
      split,
        rw [mem_filter, not_and],
        tauto,
      assumption,
  end,
  rw sum_union (h_disjoint n),
end


lemma finset_reindex_odd {f : ℕ → ℝ} (n : ℕ):
∑ l in (range (2*n)).filter(odd), f l = ∑ l in (range n), f (2*l + 1) :=
begin
  induction n with d hd,
  simp only [mul_zero, range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, sum_empty],
  rw [mul_succ, add_succ, add_succ, add_zero],
  repeat {rw range_succ},
  repeat {rewrite [finset.sum_insert]},
  repeat {rewrite [finset.filter_insert]},
  have h₁ : ¬ odd ( 2* d), by
    simp only [odd_iff_not_even, even.mul_right, even_two, not_true, not_false_iff],
  have h₂: odd (2 * d).succ, by
    {simp only [odd_iff_not_even, h₁, even_succ],
    rw ←odd_iff_not_even,
    assumption},

  rw [if_neg h₁, if_pos h₂],

  repeat {rw finset.sum_insert},
  simp only [add_right_inj],
  exact hd,
  rw [mem_filter],
  suffices :(2 * d).succ ∉ range (2 * d),
  begin
  apply not_and.mpr,
  exact not.elim this,
    end,

  rw mem_range,
  exact not_succ_lt_self,

  rw mem_range,
  exact irrefl d,
end



lemma finset_reindex_even {f : ℕ → ℝ} (n : ℕ):
∑ l in (range (2*n)).filter(even), f l = ∑ l in (range n), f (2*l) :=
begin
  induction n with d hd,
  simp only [mul_zero, range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, sum_empty],
  rw [mul_succ, add_succ, add_succ, add_zero],
  repeat {rw range_succ},
  repeat {rewrite [finset.sum_insert]},
  repeat {rewrite [finset.filter_insert]},
  have h₁ : even ( 2 * d), by exact even_two_mul d,
  have h₂ : ¬(even ((2 * d).succ)), by  {simp only [even_succ, h₁], tautology},

  rw [if_neg h₂, if_pos h₁],
  rw finset.sum_insert,
  simp only [add_right_inj],
  exact hd,

  rw [mem_filter],
  suffices : (2 * d) ∉ range (2 * d), by tauto,
  rw mem_range,
  exact irrefl (2*d),

  rw mem_range,
  exact irrefl d,
end

noncomputable def an (n : ℕ) : ℝ  := (n.factorial :ℝ )
/ ((real.sqrt(2*(n))*((n/(exp 1)))^n))

noncomputable def term (x : ℝ)(n : ℕ) : ℝ :=
   ((-1)*((-x)^(n + 1) / ((n : ℝ) + 1)) + (x^(n + 1)/((n:ℝ) + 1)))

lemma term_def : ∀ (x: ℝ) , term x =(λ n,  ((-1)*((-x)^(n + 1) / ((n : ℝ) + 1)) + (x^(n + 1)/((n:ℝ) + 1)))) :=
begin
  intros,
  refl,
end


lemma log_sum_plus_minus (x : ℝ) (hx: |x| < 1) : has_sum (λ k:ℕ,
(2:ℝ)*(1/(2*↑k + 1))*(x^(2* k + 1))) (log (1 + x) - log(1 - x)):=
begin
  have min_one_not_zero : (-1 : ℝ) ≠ ( 0 : ℝ), by linarith,
  have h_min_one_ne_one:  (-1 : ℝ) ≠ ( 1 : ℝ), by linarith,

  have h₁, from has_sum_pow_div_log_of_abs_lt_1 hx,
  have h₂', from has_sum_pow_div_log_of_abs_lt_1 (eq.trans_lt (abs_neg x) hx),
  have h₂, from (has_sum_mul_left_iff min_one_not_zero).mp h₂',
  rw [neg_one_mul, neg_neg, sub_neg_eq_add 1 x] at h₂,
  have h₃, from has_sum.add h₂ h₁,
  rw [tactic.ring.add_neg_eq_sub] at h₃,
  rw [←term_def x ] at h₃,

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


lemma bn_diff_has_sum: ∀ (n : ℕ),
has_sum (λ (k : ℕ), (1 : ℝ)/(2*k.succ + 1)*((1/(2*n.succ + 1))^2)^(k.succ))
((bn n.succ) - (bn n.succ.succ)) :=
begin
  intro m,
  have hx : ∀ (n : ℕ),  (bn n.succ) - (bn n.succ.succ) =
    ((n.succ : ℝ)+1/(2 : ℝ))* log(((n.succ.succ ): ℝ)/(n.succ:ℝ) ) - 1,
  begin
    intro n,

    have h_reorder : ∀{a b c d e f :ℝ}, a-1/(2 : ℝ)*b-c -(d-1/(2:ℝ)*e-f) = (a-d)-1/(2:ℝ)*(b-e)-(c-f),
    by {intros, ring_nf},

    rw [bn_formula, bn_formula, h_reorder ],
    repeat {rw [log_div, factorial_succ]},
    push_cast,
    repeat {rw log_mul},
    ring_nf,
    rw log_exp,
    all_goals {norm_cast},
    any_goals {field_simp},
    any_goals {exact factorial_ne_zero n},
    any_goals {exact exp_ne_zero 1},
  end,

  have h_sum₀ , from power_series_ln m.succ (succ_pos m),
  have h_nonzero : (m.succ : ℝ)+1/(2 : ℝ)≠ 0,
  by {rw cast_succ, field_simp, norm_cast, linarith},

  rw has_sum_mul_left_iff h_nonzero at h_sum₀,

  have h_inner: ∀ (b : ℕ),(((m.succ : ℝ) + 1 / 2) * (2 * (1 / (2 * ↑b + 1)) *
      (1 / (2 * ↑(m.succ) + 1)) ^ (2 * b + 1)))
      = (1 : ℝ)/(2*(b : ℝ) + 1)*((1/(2*m.succ + 1))^2)^(b) :=
  begin
    intro b,
    have  hm : ((m.succ : ℝ) > 0), by {norm_cast, exact succ_pos m},
    generalize hy : (m.succ : ℝ) = y ,
    field_simp,
    rw mul_comm,
    rw pow_add _ _ 1,
    have hy_pos : 2 * y + 1 > 0,
      by {linarith},
    generalize hz : 2 * y + 1 = z,
    rw hz at hy_pos,
    rw [←pow_mul, pow_one],
    rw ←mul_assoc,
    rw mul_comm _ z,
    rw div_mul_right,
    exact ne_of_gt hy_pos,
  end,
  have h_sum₁: has_sum (λ (b : ℕ),
  ((1 : ℝ)/(2*(b : ℝ) + 1)*((1/(2*m.succ + 1))^2)^(b)))
  (((m.succ : ℝ) + 1 / 2) * log (↑(m.succ.succ) / ↑(m.succ))) :=
  begin
    refine has_sum.has_sum_of_sum_eq _ h_sum₀,
    intros,
    use u,
    intros,
    use v',
    split,
    exact ᾰ,
    refine sum_congr rfl _,
    intros k hk,
    exact h_inner k,
  end,
  have h_sum₂ := has_sum.tendsto_sum_nat h_sum₁,
  have h_sum : tendsto
    (λ (n : ℕ), ∑ (i : ℕ) in range n.succ,
    (λ (b : ℕ), 1 / (2 * (b : ℝ) + 1) * ((1 / (2 * ↑(m.succ) + 1)) ^ 2) ^ b) i)
    at_top
    (𝓝 ((↑(m.succ) + 1 / 2) * log (↑(m.succ.succ) / ↑(m.succ)))):= succ_tendsto h_sum₂,
  simp only [] at h_sum,
  have split_zero: ∀ (n:ℕ), ∑ (i : ℕ) in range n.succ,
  1 / (2 * (i:ℝ) + 1) * ((1 / (2 * ↑(m.succ) + 1)) ^ 2) ^ i =
  (∑ (i : ℕ) in range n,
  1 / (2 * (i.succ:ℝ) + 1) * ((1 / (2 * ↑(m.succ) + 1)) ^ 2) ^ i.succ) + 1 :=
  begin
    intro n,
    rw sum_range_succ' (λ k:ℕ, 1 / (2 * (k:ℝ) + 1) * ((1 / (2 * ↑(m.succ) + 1)) ^ 2) ^ k)
    n,
    simp only [one_div, cast_succ, inv_pow₀, cast_zero, mul_zero, zero_add, pow_zero,
    inv_one, mul_one, add_left_inj],
  end,
  replace h_sum := tendsto.congr split_zero h_sum,
  replace h_sum := tendsto.add_const (-1) h_sum,
  simp only [add_neg_cancel_right] at h_sum,
  rw tactic.ring.add_neg_eq_sub _ (1 : ℝ) at h_sum,
  rw ←hx at h_sum,
  refine (summable.has_sum_iff_tendsto_nat _).mpr h_sum,
  exact summable_succ (has_sum.summable h_sum₁),
end

lemma bn_antitone: ∀ (a b : ℕ), a ≤ b → bn b.succ ≤ bn a.succ :=
begin
  apply antitone_nat_of_succ_le,
  intro n,
  refine sub_nonneg.mp _,
  rw ←succ_eq_add_one,
  refine has_sum.nonneg _ (bn_diff_has_sum n),
  norm_num,
  simp only [one_div],
  intro b,
  refine mul_nonneg _ _,
  all_goals {refine inv_nonneg.mpr _},
  all_goals {norm_cast},
  exact zero_le (2 * (b + 1) + 1),
  exact zero_le (((2 * (n + 1) + 1) ^ 2) ^ succ b),
end

lemma bn_diff_le_geo_sum: ∀ (n : ℕ),
bn n.succ - bn n.succ.succ ≤
(1/(2*n.succ + 1))^2/(1 - (1/(2*n.succ + 1))^2) :=
begin
  intro n,
  have h := bn_diff_has_sum n,
  have g : has_sum
  (λ (k : ℕ), ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ)
  ((1/(2*n.succ + 1))^2/(1 - (1/(2*n.succ + 1))^2)) :=
  begin
    have h_pow_succ := λ (k:ℕ),
    symm (pow_succ ((1 / (2 * ((n:ℝ) + 1) + 1)) ^ 2)  k),
    have h_nonneg: 0 ≤ ((1 / (2 * (n.succ:ℝ) + 1)) ^ 2) :=
    begin
      simp only [cast_succ, one_div, inv_pow₀, inv_nonneg],
      norm_cast,
      simp only [zero_le'],
    end,
    have hlt:  ((1 / (2 * (n.succ:ℝ) + 1)) ^ 2) < 1 :=
    begin
      simp only [cast_succ, one_div, inv_pow₀],
      refine inv_lt_one _,
      norm_cast,
      simp only [nat.one_lt_pow_iff, ne.def, zero_eq_bit0,
        nat.one_ne_zero, not_false_iff, lt_add_iff_pos_left, canonically_ordered_comm_semiring.mul_pos,
        succ_pos', and_self],
    end,
    have h_geom := has_sum_geometric_of_lt_1 h_nonneg hlt,
    have h_geom' :=
    has_sum.mul_left ((1 / (2 * (n.succ:ℝ) + 1)) ^ 2) h_geom,
    norm_num at h_geom',
    norm_num at h_pow_succ,
    have h_geom'' :
    has_sum (λ (b : ℕ), (1 / ((2 * ((n:ℝ) + 1) + 1) ^ 2) ^ b.succ))
    (1 / (2 * ((n:ℝ) + 1) + 1) ^ 2 * (1 - 1 / (2 * (↑n + 1) + 1) ^ 2)⁻¹) :=
    begin
      refine has_sum.has_sum_of_sum_eq _ h_geom',
      intros,
      use u,
      intros,
      use v',
      split,
      exact ᾰ,
      refine sum_congr rfl _,
      intros k hk,
      exact h_pow_succ k,
    end,
    norm_num,
    exact h_geom'',
  end,
  have hab: ∀ (k:ℕ),
  (1 / (2 * (k.succ : ℝ) + 1)) * ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ
  ≤  ((1 / (2*(n.succ : ℝ) + 1)) ^ 2) ^ k.succ:=
  begin
    intro k,
    have h_zero_le: 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ :=
    begin
      simp only [cast_succ, one_div, inv_pow₀, inv_nonneg],
      norm_cast,
      simp only [zero_le'],
    end,
    have h_left: 1 / (2 * (k.succ:ℝ) + 1) ≤ 1 :=
    begin
      simp only [cast_succ, one_div],
      refine inv_le_one _,
      norm_cast,
      simp only [le_add_iff_nonneg_left, zero_le'],
    end,
    exact mul_le_of_le_one_left h_zero_le h_left,
  end,
  exact has_sum_le hab h g,
end

lemma bn_sub_bn_succ: ∀ (n : ℕ),
bn n.succ - bn n.succ.succ ≤ 1/(4*n.succ*(n.succ.succ)) :=
begin
  intro n,
  refine le_trans (bn_diff_le_geo_sum n) _,
  have h₁: 0 < 4 * (n.succ : ℝ) * ↑(n.succ.succ) :=
  begin
    norm_cast,
    simp only [canonically_ordered_comm_semiring.mul_pos,
    succ_pos', and_self],
  end,
  have h₂: 0 < 1 - (1 / (2 * (n.succ : ℝ) + 1)) ^ 2 :=
  begin
    refine sub_pos.mpr _,
    refine (sq_lt_one_iff _).mpr _,
    rw one_div,
    refine inv_nonneg.mpr _,
    norm_cast,
    exact zero_le (2 * succ n + 1),
    refine (div_lt_one _).mpr _,
    all_goals {norm_cast},
    linarith,
    refine lt_add_of_pos_left 1 _,
    refine (1:ℕ).succ_mul_pos _,
    exact succ_pos n,
  end,
  refine (le_div_iff' h₁).mpr _,
  rw mul_div (4 * (n.succ:ℝ) * ↑(n.succ.succ))
    ((1 / (2 * ↑(n.succ) + 1)) ^ 2) (1 - (1 / (2 * (n.succ:ℝ) + 1)) ^ 2),
  refine (div_le_one h₂).mpr _,
  norm_num,
  rw mul_div,
  have h₃: 0 < (2 * ((n : ℝ) + 1) + 1) ^ 2 :=
  begin
    rw sq,
    norm_cast,
    simp only [canonically_ordered_comm_semiring.mul_pos,
    succ_pos', and_self],
  end,
  refine (div_le_iff' h₃).mpr _,
  rw mul_sub,
  norm_num,
  refine le_sub.mp _,
  rw mul_one_div,
  refine (div_le_iff' h₃).mpr _,
  refine (le_mul_iff_one_le_right h₃).mpr _,
  refine le_sub_iff_add_le.mpr _,
  norm_cast,
  rw sq,
  linarith,
end

lemma bn_bounded_aux: ∀ (n : ℕ), bn 1 - bn n.succ ≤ 1/4 :=
begin
  let bn': (ℕ → ℝ) :=  λ (k : ℕ), bn k.succ,
  intro n,
  calc
  bn 1 - bn n.succ = bn' 0 - bn' n : rfl
   ... = ∑ i in range n, (bn' i - bn' (i + 1)) : by rw ←(sum_range_sub' bn' n)
   ... = ∑ i in range n, (bn i.succ - bn i.succ.succ) : rfl
   ... ≤ ∑ i in range n, 1/(4*i.succ*(i.succ.succ)) :
   begin
     refine sum_le_sum _,
     intros k hk,
     exact bn_sub_bn_succ k,
   end
   ... = ∑ i in range n, (1/4)*(1/(i.succ*(i.succ.succ))) :
   begin
     have hi: ∀ (i:ℕ), (1 : ℝ)/(4*i.succ*(i.succ.succ)) = (1/4)*(1/(i.succ*(i.succ.succ))) :=
     begin
       intro i,
       norm_cast,
       field_simp,
       simp only [one_div, inv_inj],
       ring,
     end,
    refine sum_congr rfl _,
    intros k hk,
    exact hi k,
   end
   ... = 1/4 * ∑ i in range n, 1/(i.succ*(i.succ.succ)) :
   begin
     rw mul_sum,
   end
   ... ≤ 1/4 * 1 :
   begin
     refine (mul_le_mul_left _).mpr _,
     simp only [one_div, inv_pos, zero_lt_bit0, zero_lt_one],
     exact partial_sum_consecutive_reciprocals n,
   end
   ... = 1/4 : by rw mul_one,
end

lemma bn_bounded_by_constant: ∀  (n : ℕ), bn n.succ ≥ 3/(4:ℝ) - 1/2*log 2 :=
begin
  intro n,
  calc
  bn n.succ ≥ bn 1 - 1/4 :sub_le.mp (bn_bounded_aux n)
   ... = (log((1:ℕ).factorial) - 1/2*log(2 * (1 : ℕ)) - (1:ℕ)*log((1:ℕ)/(exp 1))) - 1/4:
   by rw bn_formula 0
   ... = 0 - 1/2*log(2) - log(1/(exp 1)) - 1/4 : by simp only [factorial_one, cast_one, log_one, one_div, mul_one, log_inv, log_exp, mul_neg]
   ... = -1/2*log(2) - log(1/(exp 1)) - 1/4: by ring
   ... = -1/2*log(2) + 1 - 1/4: by simp only [one_div, log_inv, log_exp, sub_neg_eq_add]
   ... =  -1/2*log(2) + 3/4: by ring
   ... =  3/(4:ℝ) - 1/2*log 2: by ring,
end

lemma bn_has_lower_bound:(lower_bounds (set.range (λ (k:ℕ), bn k.succ))).nonempty :=
begin
   use  3/(4:ℝ) - 1/2*log 2 ,
   intros,
   rw lower_bounds,
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact bn_bounded_by_constant,
end

lemma monotone_convergence (bn : ℕ → ℝ) (h_sd: ∀ (a b : ℕ), a ≤ b → bn b ≤ bn a)
(h_bounded: (lower_bounds (set.range bn)).nonempty): ∃ (b : ℝ), tendsto bn at_top (𝓝  b)  :=
begin
 let x := (Inf (set.range bn)),
 have h: is_glb (set.range bn) x :=
 begin
   refine real.is_glb_Inf (set.range bn) (set.range_nonempty bn) h_bounded,
 end,
 use x,
 refine tendsto_at_top_is_glb _ _,
 rw antitone,
 exact h_sd,
 exact h,
end

lemma bn_has_limit_b: ∃ (b : ℝ),
tendsto (λ (n : ℕ),  bn n.succ)  at_top (𝓝  b) :=
begin
  exact monotone_convergence (λ (k:ℕ), bn k.succ) bn_antitone bn_has_lower_bound,
end

/-an_pos can not be proven if we allow n = 0
corrected version below, but dependent lemmas need to be adjusted-/

lemma  an'_pos: ∀ (n : ℕ), 0 < an n.succ :=
begin
  intro n,
  rw an,
  norm_cast,
  simp only [sqrt_mul', cast_nonneg, div_pow],
  field_simp,
  have h₁: 0 < ((n : ℝ) + 1)*((n).factorial : ℝ) :=
  begin
    norm_cast,
    apply mul_pos,
    exact succ_pos n,
    exact factorial_pos (n),
  end,
  have h₂: 0 < exp(1)^n.succ := (pow_pos ((1:ℝ).exp_pos)) n.succ,
  have h₃: 0 < sqrt (2 :ℝ) * sqrt (↑n + 1) * (↑n + 1) ^ (n + 1) :=
  begin
    apply mul_pos,
    apply mul_pos,
    simp only [real.sqrt_pos, zero_lt_bit0, zero_lt_one],
    simp only [real.sqrt_pos, cast_pos],
    norm_cast,
    exact succ_pos n,
    apply pow_pos,
    norm_cast,
    exact succ_pos n,
  end,
  apply mul_pos,
  apply mul_pos h₁ h₂,
  simp only [inv_pos],
  exact h₃,
end

lemma an'_bounded_by_pos_constant:
∀ (n : ℕ), exp(3/(4:ℝ) - 1/2*log 2) ≤ an n.succ:=
begin
  intro n,
  rw  ←(le_log_iff_exp_le (an'_pos n)),
  exact bn_bounded_by_constant n,
end

lemma an'_antitone: ∀ (a b : ℕ), a ≤ b → an b.succ ≤ an a.succ :=
begin
  intros a b,
  intro hab,
  have h := bn_antitone a b hab,
  rw bn at h,
  rw bn at h,
  exact (log_le_log (an'_pos b) (an'_pos a)).mp h,
end


lemma an'_has_lower_bound:
(lower_bounds (set.range (λ (k:ℕ), an k.succ))).nonempty :=
begin
   use  exp(3/(4:ℝ) - 1/2*log 2),
   intros,
   rw lower_bounds,
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact an'_bounded_by_pos_constant,
end

lemma an'_has_limit_a :  ∃ (a : ℝ), tendsto
(λ (n : ℕ),  an n.succ) at_top (𝓝 a) :=
begin
  exact monotone_convergence (λ (k:ℕ), an k.succ) an'_antitone an'_has_lower_bound,
end

lemma an_has_limit_a: ∃ (a : ℝ), tendsto
(λ (n : ℕ),  an n)
  at_top (𝓝  a) :=
begin
  have ha := an'_has_limit_a,
  cases ha with x hx,
  rw ←tendsto_succ an x at hx,
  use x,
  exact hx,
end

lemma an_has_pos_limit_a: ∃ (a : ℝ), 0 < a ∧ tendsto
(λ (n : ℕ),  an n)
  at_top (𝓝  a) :=
begin
  have h:= an_has_limit_a,
  cases h with a ha,
  use a,
  split,
  let an' : ℕ → ℝ := λ n, an n.succ,
  rw tendsto_succ an a at ha,
  have a_is_glb: is_glb (set.range an') a := is_glb_of_tendsto_at_top an'_antitone ha,
  have e_lower_bound:   exp(3/(4:ℝ) - 1/2*log 2) ∈ lower_bounds (set.range an') :=
  begin
    intros x hx,
    simp only [set.mem_range] at hx,
    cases hx with k hk,
    rw ←hk,
    exact an'_bounded_by_pos_constant k,
  end,
  have e_le: exp(3/(4:ℝ) - 1/2*log 2) ≤ a := (le_is_glb_iff a_is_glb).mpr e_lower_bound,
  have e_pos: 0 < exp(3/(4:ℝ) - 1/2*log 2) := (3 / 4 - 1 / 2 * log 2).exp_pos,
  exact gt_of_ge_of_gt e_le e_pos,
  exact ha,
end
