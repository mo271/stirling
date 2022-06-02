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

import part1a

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat


-- part 1 of https://proofwiki.org/wiki/Stirling%27s_Formula
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
  refine (summable.has_sum_iff_tendsto_nat _).mpr h_sum,
  exact (summable_nat_add_iff 1).mpr (has_sum.summable h_sum₁),
end

--uses bn, bn_diff_has_sum
lemma bn_antitone : ∀ (a b : ℕ), a ≤ b → bn b.succ ≤ bn a.succ :=
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
    have h_left : 1 / (2 * (k.succ:ℝ) + 1) ≤ 1 :=
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
  refine le_trans (bn_diff_le_geo_sum n) _,
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
  refine (le_div_iff' h₁).mpr _,
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
  refine (div_le_iff' h₃).mpr _,
  refine (le_mul_iff_one_le_right h₃).mpr _,
  refine le_sub_iff_add_le.mpr _,
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
     simp only [one_div, inv_pos, zero_lt_bit0, zero_lt_one],
     exact partial_sum_consecutive_reciprocals n,
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
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact bn_bounded_by_constant,
end

--not in lib?
lemma monotone_convergence (bn : ℕ → ℝ) (h_sd: ∀ (a b : ℕ), a ≤ b → bn b ≤ bn a)
  (h_bounded : (lower_bounds (set.range bn)).nonempty) : ∃ (b : ℝ), tendsto bn at_top (𝓝 b) :=
begin
 use Inf (set.range bn),
 refine tendsto_at_top_is_glb h_sd (real.is_glb_Inf (set.range bn)
   (set.range_nonempty bn) h_bounded),
end

--uses bn, bn_antitone, bn_has_lower_bound
lemma bn_has_limit_b : ∃ (b : ℝ),
tendsto (λ (n : ℕ),  bn n.succ) at_top (𝓝 b) :=
begin
  exact monotone_convergence (λ (k : ℕ), bn k.succ) bn_antitone bn_has_lower_bound,
end

--uses an,
lemma an'_pos : ∀ (n : ℕ), 0 < an n.succ :=
begin
  intro n,
  rw an,
  norm_cast,
  simp only [sqrt_mul', cast_nonneg, div_pow],
  field_simp,
  have h₁ : 0 < ((n : ℝ) + 1) * (n.factorial : ℝ) :=
  begin
    norm_cast,
    exact mul_pos n.succ_pos n.factorial_pos,
  end,
  have h₂ : 0 < exp 1 ^ n.succ := (pow_pos ((1 : ℝ).exp_pos)) n.succ,
  have h₃ : 0 < sqrt (2 : ℝ) * sqrt ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (n + 1) :=
  begin
    apply mul_pos,
    { apply mul_pos,
    simp only [real.sqrt_pos, zero_lt_bit0, zero_lt_one],
    simp only [real.sqrt_pos, cast_pos],
    norm_cast,
    exact succ_pos n},
    apply pow_pos,
    norm_cast,
    exact succ_pos n,
  end,
  exact mul_pos (mul_pos h₁ h₂) (inv_pos.mpr h₃),
end

--uses an, bn_bounded_by_constant
lemma an'_bounded_by_pos_constant : ∀ (n : ℕ), exp (3 / (4 : ℝ) - 1 / 2 * log 2) ≤ an n.succ :=
begin
  intro n,
  rw ← (le_log_iff_exp_le (an'_pos n)),
  exact bn_bounded_by_constant n,
end

--uses an, bn, bn_antitone, an'
lemma an'_antitone : ∀ (a b : ℕ), a ≤ b → an b.succ ≤ an a.succ :=
begin
  intros a b,
  intro hab,
  have h := bn_antitone a b hab,
  rw bn at h,
  rw bn at h,
  exact (log_le_log (an'_pos b) (an'_pos a)).mp h,
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
lemma an'_has_limit_a :  ∃ (a : ℝ), tendsto (λ (n : ℕ), an n.succ) at_top (𝓝 a) :=
begin
  exact monotone_convergence (λ (k : ℕ), an k.succ) an'_antitone an'_has_lower_bound,
end

--uses an'_has_limit_a
lemma an_has_limit_a : ∃ (a : ℝ), tendsto (λ (n : ℕ), an n) at_top (𝓝 a) :=
begin
  have ha := an'_has_limit_a,
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
  have a_is_glb : is_glb (set.range an') a := is_glb_of_tendsto_at_top an'_antitone ha,
  have e_lower_bound : exp (3 / (4 : ℝ) - 1 / 2 * log 2) ∈ lower_bounds (set.range an') :=
  begin
    intros x hx,
    rw [set.mem_range] at hx,
    cases hx with k hk,
    rw ←hk,
    exact an'_bounded_by_pos_constant k,
  end,
  have e_le : exp (3 / (4 : ℝ) - 1 / 2 * log 2) ≤ a := (le_is_glb_iff a_is_glb).mpr e_lower_bound,
  have e_pos : 0 < exp (3 / (4 : ℝ) - 1 / 2 * log 2) := (3 / 4 - 1 / 2 * log 2).exp_pos,
  exact gt_of_ge_of_gt e_le e_pos,
  exact ha,
end
