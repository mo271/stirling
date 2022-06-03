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
import order.filter.basic
import order.bounded_order
import analysis.special_functions.pow

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums
open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open nat
open filter


/-- Perhaps something to add as rat.cast_sum in more generality (see below) in mathlib?!-/
lemma rat_cast_sum (s : finset ℕ) (f : ℕ → ℚ) :
  ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : ℝ)) :=
  (rat.cast_hom ℝ).map_sum f s
-- @[simp, norm_cast] lemma rat_cast_sum [add_comm_monoid β] [has_one β]
-- (s : finset α) (f : α → ℚ) :
-- ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) := by sorry

/-- **Sum of the Reciprocals of the Triangular Numbers**
 from archive TODO: include in some form mathlib-/
lemma inverse_triangle_sum :
  ∀ n, ∑ k in range n, (2 : ℚ) / (k * (k + 1)) = if n = 0 then 0 else 2 - (2 : ℚ) / n :=
begin
  refine sum_range_induction _ _ (if_pos rfl) _,
  rintro (_|n), { rw [if_neg, if_pos]; norm_num },
  simp_rw [if_neg (nat.succ_ne_zero _), nat.succ_eq_add_one],
  have A : (n + 1 + 1 : ℚ) ≠ 0, by { norm_cast, norm_num },
  push_cast,
  field_simp [nat.cast_add_one_ne_zero],
  ring,
end

lemma partial_sum_consecutive_reciprocals:
 ∀ n, ∑ k in range n, (1 : ℚ) / (k.succ * (k.succ.succ)) ≤ 1 :=
 begin
   intro n,
   rw [←(mul_le_mul_left (zero_lt_two)), mul_sum],
   have h: ∀ (k : ℕ), k ∈ (range n) →
     2*((1 : ℚ) / (k.succ * (k.succ.succ))) = 2 / (k.succ * (k.succ.succ)) :=
   begin
     intros k hk,
     rw [mul_div],
     rw [mul_one (2:ℚ)],
  end,
  rw finset.sum_congr rfl h,
  have h₁ := inverse_triangle_sum n.succ,
  rw sum_range_succ' at h₁,
  norm_num at *,
  rw h₁,
  simp only [sub_le_self_iff],
  refine (le_div_iff _).mpr (_),
  exact (cast_lt.mpr n.succ_pos),
  rw [zero_mul],
  exact zero_le_two,
  exact rat.nontrivial,
 end
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
import order.bounded_order
import analysis.special_functions.pow

import part1a

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
-- second section of part 1

-- uses bn, bn_formula,
lemma bn_diff_has_sum (m : ℕ) :
  has_sum (λ (k : ℕ), (1 : ℝ) / (2 * k.succ + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ (k.succ))
  ((bn m.succ) - (bn m.succ.succ)) :=
begin
  have hx : ∀ (n : ℕ), (bn n.succ) - (bn n.succ.succ) =
    ((n.succ : ℝ) + 1 / (2 : ℝ)) * log(((n.succ.succ) : ℝ) / (n.succ : ℝ)) - 1,
  begin
    intro n,
    have h_reorder : ∀ {a b c d e f : ℝ},
    a - 1 / (2 : ℝ) * b - c -(d - 1 / (2 : ℝ) * e - f) = (a - d) - 1 / (2 : ℝ) * (b - e) - (c - f),
    by {intros, ring_nf},
    rw [bn_formula, bn_formula, h_reorder],
    repeat {rw [log_div, factorial_succ]},
    push_cast,
    repeat {rw log_mul},
    --ring_nf,
    rw log_exp,
    ring_nf,
    all_goals {norm_cast},
    all_goals {try {refine mul_ne_zero _ _}, try {exact succ_ne_zero _}},
    any_goals {exact factorial_ne_zero n},
    any_goals {exact exp_ne_zero 1},
  end,
  have h_sum₀, from power_series_ln m.succ (succ_pos m),
  have h_nonzero : (m.succ : ℝ) + 1 / (2 : ℝ) ≠ 0,
  by {rw cast_succ, field_simp, norm_cast, linarith}, --there has to be a better way...
  rw has_sum_mul_left_iff h_nonzero at h_sum₀,
  have h_inner: ∀ (b : ℕ) , (((m.succ : ℝ) + 1 / 2) * (2 * (1 / (2 * (b : ℝ) + 1)) *
      (1 / (2 * (m.succ : ℝ) + 1)) ^ (2 * b + 1)))
      = (1 : ℝ) / (2 * (b : ℝ) + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ b :=
  begin
    intro b,
    rw [←pow_mul, pow_add],
    have : 2 * (b : ℝ) + 1     ≠ 0, by {norm_cast, exact succ_ne_zero (2*b)},
    have : 2 * (m.succ :ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2*m.succ)},
    field_simp,
    rw mul_comm _ (2 : ℝ),
    exact mul_rotate' _ _ _,
  end,
  have h_sum₁ : has_sum (λ (b : ℕ),
    ((1 : ℝ) / (2 * (b : ℝ) + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ b))
    (((m.succ : ℝ) + 1 / 2) * log ((m.succ.succ : ℝ) / (m.succ : ℝ))) :=
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
    (λ (b : ℕ), 1 / (2 * (b : ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ b) i)
    at_top
    (𝓝 (((m.succ : ℝ) + 1 / 2) * log ((m.succ.succ : ℝ) / (m.succ : ℝ)))) :=
    h_sum₂.comp (tendsto_add_at_top_nat 1),
  have split_zero: ∀ (n : ℕ), ∑ (i : ℕ) in range n.succ,
  1 / (2 * (i : ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ i =
  (∑ (i : ℕ) in range n,
  1 / (2 * (i.succ:ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ i.succ) + 1 :=
  begin
    intro n,
    rw sum_range_succ' (λ (k : ℕ), 1 / (2 * (k:ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ k) n,
    simp only [one_div, cast_succ, inv_pow₀, cast_zero, mul_zero, zero_add, pow_zero,
    inv_one, mul_one, add_left_inj],
  end,
  replace h_sum := tendsto.congr split_zero h_sum,
  replace h_sum := tendsto.add_const (-1) h_sum,
  simp only [add_neg_cancel_right] at h_sum,
  rw tactic.ring.add_neg_eq_sub _ (1 : ℝ) at h_sum,
  rw ← hx at h_sum,
  refine (summable.has_sum_iff_tendsto_nat
    ((summable_nat_add_iff 1).mpr (has_sum.summable h_sum₁))).mpr h_sum,
end

--uses bn, bn_diff_has_sum
lemma bn_antitone : ∀ (n m : ℕ), n ≤ m → bn m.succ ≤ bn n.succ :=
begin
  apply antitone_nat_of_succ_le,
  intro n,
  refine sub_nonneg.mp _,
  rw ←succ_eq_add_one,
  refine has_sum.nonneg _ (bn_diff_has_sum n),
  norm_num,
  simp only [one_div],
  intro m,
  refine mul_nonneg _ _,
  all_goals {refine inv_nonneg.mpr _},
  all_goals {norm_cast},
  exact zero_le (2 * (m + 1) + 1),
  exact zero_le (((2 * (n + 1) + 1) ^ 2) ^ succ m),
end

--uses bn, bn_diff_has_sum,
lemma bn_diff_le_geo_sum : ∀ (n : ℕ),
  bn n.succ - bn n.succ.succ ≤ (1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2) :=
begin
  intro n,
  have h := bn_diff_has_sum n,
  have g : has_sum
  (λ (k : ℕ), ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ)
  ((1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2)) :=
  begin
    have h_pow_succ := λ (k : ℕ),
    symm (pow_succ ((1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2)  k),
    have h_nonneg: 0 ≤ ((1 / (2 * (n.succ:ℝ) + 1)) ^ 2) :=
    begin
      rw [cast_succ, one_div, inv_pow₀, inv_nonneg],
      norm_cast,
      exact zero_le',
    end,
    have hlt : ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) < 1 :=
    begin
      simp only [cast_succ, one_div, inv_pow₀],
      refine inv_lt_one _,
      norm_cast,
      simp only [nat.one_lt_pow_iff, ne.def, zero_eq_bit0,
        nat.one_ne_zero, not_false_iff, lt_add_iff_pos_left, canonically_ordered_comm_semiring.mul_pos,
        succ_pos', and_self],
    end,
    have h_geom := has_sum_geometric_of_lt_1 h_nonneg hlt,
    have h_geom' := has_sum.mul_left ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) h_geom,
    norm_num at h_geom',
    norm_num at h_pow_succ,
    have h_geom'' :
      has_sum (λ (b : ℕ), (1 / ((2 * ((n : ℝ) + 1) + 1) ^ 2) ^ b.succ))
      (1 / (2 * ((n : ℝ) + 1) + 1) ^ 2 * (1 - 1 / (2 * ((n : ℝ) + 1) + 1) ^ 2)⁻¹) :=
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
  have hab :
    ∀ (k : ℕ), (1 / (2 * (k.succ : ℝ) + 1)) * ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ ≤
    ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ :=
  begin
    intro k,
    have h_zero_le : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ :=
    begin
      simp [cast_succ, one_div, inv_pow₀, inv_nonneg],
      norm_cast,
      exact zero_le',
    end,
    have h_left : 1 / (2 * (k.succ : ℝ) + 1) ≤ 1 :=
    begin
      simp only [cast_succ, one_div],
      refine inv_le_one _,
      norm_cast,
      exact (le_add_iff_nonneg_left 1).mpr zero_le',
    end,
    exact mul_le_of_le_one_left h_zero_le h_left,
  end,
  exact has_sum_le hab h g,
end

--uses bn, sq, succ_pos', bn_diff_le_geo_sum
lemma bn_sub_bn_succ : ∀ (n : ℕ),
bn n.succ - bn n.succ.succ ≤ 1 / (4 * n.succ * n.succ.succ) :=
begin
  intro n,
  have h₁ : 0 < 4 * (n.succ : ℝ) * (n.succ.succ : ℝ) :=
  begin
    norm_cast,
    simp only [canonically_ordered_comm_semiring.mul_pos,
    succ_pos', and_self],
  end,
  have h₂ : 0 < 1 - (1 / (2 * (n.succ : ℝ) + 1)) ^ 2 :=
  begin
    refine sub_pos.mpr _,
    refine (sq_lt_one_iff _).mpr _,
    { rw one_div,
    refine inv_nonneg.mpr _,
    norm_cast,
    exact zero_le (2 * succ n + 1)},
    { refine (div_lt_one _).mpr _,
    all_goals {norm_cast},
    linarith,
    refine lt_add_of_pos_left 1 _,
    refine (1 : ℕ).succ_mul_pos _,
    exact succ_pos n},
  end,
  refine le_trans (bn_diff_le_geo_sum n) ((le_div_iff' h₁).mpr _),
  rw mul_div (4 * (n.succ : ℝ) * (n.succ.succ : ℝ))
    ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) (1 - (1 / (2 * (n.succ : ℝ) + 1)) ^ 2),
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
  refine (div_le_iff' h₃).mpr ((le_mul_iff_one_le_right h₃).mpr
    (le_sub_iff_add_le.mpr _)),
  norm_cast,
  rw sq,
  linarith,
end

--uses bn, bn_sub_bn_succ, partial_sum_consecutive_reciprocals
lemma bn_bounded_aux : ∀ (n : ℕ), bn 1 - bn n.succ ≤ 1 / 4 :=
begin
  let bn' : (ℕ → ℝ) :=  λ (k : ℕ), bn k.succ,
  intro n,
  calc
  bn 1 - bn n.succ = bn' 0 - bn' n : rfl
   ... = ∑ i in range n, (bn' i - bn' (i + 1))          : by rw ← (sum_range_sub' bn' n)
   ... = ∑ i in range n, (bn i.succ - bn i.succ.succ)   : rfl
   ... ≤ ∑ i in range n, 1 / (4 * i.succ * i.succ.succ) :
   begin
     refine sum_le_sum _,
     intros k hk,
     exact bn_sub_bn_succ k,
   end
   ... = ∑ i in range n, (1 / 4) * (1 / (i.succ * i.succ.succ)) :
   begin
     have hi : ∀ (i : ℕ), (1 : ℝ) / (4 * i.succ * i.succ.succ) =
      (1 / 4) * (1 / (i.succ * i.succ.succ)) :=
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
   ... = 1 / 4 * ∑ i in range n, 1 / (i.succ * i.succ.succ) : by rw mul_sum
   ... ≤ 1 / 4 * 1 :
   begin
     refine (mul_le_mul_left _).mpr _,
     exact div_pos one_pos four_pos,
     have g: (((∑ (k : ℕ) in range n, 1 / ((((k.succ))) * ((k.succ.succ)))):ℚ):ℝ)
     ≤ ((1:ℚ):ℝ)  :=
     rat.cast_le.mpr (partial_sum_consecutive_reciprocals n),
     rw rat_cast_sum at g,
     rw rat.cast_one at g,
     push_cast at g,
     push_cast,
     exact g,
   end
   ... = 1 / 4 : by rw mul_one,
end

--uses bn_bounded_aux, bn, bn_formula
lemma bn_bounded_by_constant : ∀ (n : ℕ), bn n.succ ≥ 3 / (4 : ℝ) - 1 / 2 * log 2 :=
begin
  intro n,
  calc
  bn n.succ ≥ bn 1 - 1 / 4 : sub_le.mp (bn_bounded_aux n)
   ... = (log ((1 : ℕ).factorial) - 1 / 2 * log (2 * (1 : ℕ)) - (1 : ℕ) *
          log ((1 : ℕ) / (exp 1))) - 1 / 4 : by rw bn_formula 0
   ... = 0 - 1 / 2 * log 2 - log (1 / (exp 1)) - 1 / 4 :
      by simp only [factorial_one, cast_one, log_one, one_div, mul_one, log_inv, log_exp, mul_neg]
   ... = -1 / 2 * log 2 - log (1 / (exp 1)) - 1 / 4 : by ring
   ... = -1 / 2 * log 2 + 1 - 1 / 4  : by simp only [one_div, log_inv, log_exp, sub_neg_eq_add]
   ... = -1 / 2 * log 2 + 3 / 4      : by ring
   ... = 3 / (4 : ℝ) - 1 / 2 * log 2 : by ring,
end

--uses bn, bn_bounded_by_constant
lemma bn_has_lower_bound : (lower_bounds (set.range (λ (k : ℕ), bn k.succ))).nonempty :=
begin
   use 3 / (4 : ℝ) - 1 / 2 * log 2,
   intros,
   rw lower_bounds,
   rw [set.mem_set_of_eq],
   simp only [set.mem_range, forall_apply_eq_imp_iff', forall_exists_index],
   exact bn_bounded_by_constant,
end

--not in lib?
lemma monotone_convergence (bn : ℕ → ℝ) (h_sd: ∀ (n m : ℕ), n ≤ m → bn m ≤ bn n)
  (h_bounded : (lower_bounds (set.range bn)).nonempty) : ∃ (m : ℝ), tendsto bn at_top (𝓝 m) :=
begin
 use Inf (set.range bn),
 refine tendsto_at_top_is_glb h_sd (real.is_glb_Inf (set.range bn)
   (set.range_nonempty bn) h_bounded),
end

--uses bn, bn_antitone, bn_has_lower_bound
lemma bn_has_limit_b : ∃ (n : ℝ),
tendsto (λ (m : ℕ),  bn m.succ) at_top (𝓝 n) :=
begin
  exact monotone_convergence (λ (k : ℕ), bn k.succ) bn_antitone bn_has_lower_bound,
end

--uses an,
lemma an'_pos : ∀ (n : ℕ), 0 < an n.succ :=
begin
  intro n,
  rw an,
  exact div_pos (cast_pos.mpr (factorial_pos n.succ))
    (mul_pos ((real.sqrt_pos).mpr (mul_pos two_pos (cast_pos.mpr (succ_pos n))))
    (pow_pos (div_pos (cast_pos.mpr (succ_pos n)) (exp_pos 1)) n.succ)),
end

--uses an, bn_bounded_by_constant
lemma an'_bounded_by_pos_constant : ∀ (n : ℕ), exp (3 / (4 : ℝ) - 1 / 2 * log 2) ≤ an n.succ :=
begin
  intro n,
  rw ← (le_log_iff_exp_le (an'_pos n)),
  exact bn_bounded_by_constant n,
end

--uses an, bn, bn_antitone, an'
lemma an'_antitone : ∀ (n m : ℕ), n ≤ m → an m.succ ≤ an n.succ :=
begin
  intros n m,
  intro hab,
  have h := bn_antitone n m hab,
  rw bn at h,
  rw bn at h,
  exact (log_le_log (an'_pos m) (an'_pos n)).mp h,
end

--uses an, an'_bounded_by_pos_constant
lemma an'_has_lower_bound : (lower_bounds (set.range (λ (k : ℕ), an k.succ))).nonempty :=
begin
   use exp (3 / (4 : ℝ) - 1 / 2 * log 2),
   intros,
   rw lower_bounds,
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact an'_bounded_by_pos_constant,
end

--uses an'_antitone, an'_has_lower_bound,
lemma an_has_limit_a : ∃ (a : ℝ), tendsto (λ (n : ℕ), an n) at_top (𝓝 a) :=
begin
  have ha := monotone_convergence (λ (k : ℕ), an k.succ) an'_antitone an'_has_lower_bound,
  cases ha with x hx,
  rw ← tendsto_succ an x at hx,
  use x,
  exact hx,
end

--uses an_has_limit_a, an'_antitone, an, an'_bounded_by_pos_constant
lemma an_has_pos_limit_a : ∃ (a : ℝ), 0 < a ∧ tendsto (λ (n : ℕ), an n) at_top (𝓝 a) :=
begin
  have h := an_has_limit_a,
  cases h with a ha,
  use a,
  split,
  let an' : ℕ → ℝ := λ n, an n.succ,
  rw tendsto_succ an a at ha,
  have e_lower_bound : exp (3 / (4 : ℝ) - 1 / 2 * log 2) ∈ lower_bounds (set.range an') :=
  begin
    intros x hx,
    rw [set.mem_range] at hx,
    cases hx with k hk,
    rw ←hk,
    exact an'_bounded_by_pos_constant k,
  end,
  exact gt_of_ge_of_gt ((le_is_glb_iff (is_glb_of_tendsto_at_top an'_antitone ha)).mpr
    e_lower_bound) (3 / 4 - 1 / 2 * log 2).exp_pos,
  exact ha,
end
