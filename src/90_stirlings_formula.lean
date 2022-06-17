/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn.
-/
import tactic
import analysis.special_functions.log
import analysis.special_functions.pow
import algebra.big_operators.basic
import algebra.big_operators.intervals
import data.finset.sum
import data.fintype.basic
import data.real.basic
import data.real.pi.wallis
import order.filter
import order.filter.basic
import order.bounded_order
import topology.instances.real
import topology.instances.ennreal

/-!
# Stirling's formula

This file proves Theorem 90 from the [100 Theorem List] <https://www.cs.ru.nl/~freek/100/>.
It states that `n!` grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.


## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.#check

We proceed in two parts.#check
### Part 1
We consider the fraction sequence $a_n$ of fractions `n!` over $\sqrt{2\pi n}(\frac{n}{e})^n$ and
proves that this sequence converges against a real, positve number `a`. For this the two main
ingredients are
 - taking the logarithm of the sequence and
 - use the series expansion of `log(1 + x)`.

### Part 2
We use the fact that the series defined in part 1 converges againt a real number `a` and prove that
`a = √π`. Here the main ingredient is the convergence of the Wallis product.
-/

namespace stirling

open_locale big_operators -- notation ∑ for finite sums
open_locale classical real topological_space nnreal ennreal filter big_operators
open real
open finset
open nat
open filter


/-- TODO: Perhaps something to add as rat.cast_sum in more generality (see below) in mathlib?!-/
lemma rat_cast_sum (s : finset ℕ) (f : ℕ → ℚ) :
  ↑(∑ n in s, f n : ℚ) = (∑ n in s, (f n : ℝ)) :=
  (rat.cast_hom ℝ).map_sum f s
-- @[simp, norm_cast] lemma rat_cast_sum [add_comm_monoid β] [has_one β]
-- (s : finset α) (f : α → ℚ) :
-- ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) := by sorry

/-- **Sum of the Reciprocals of the Triangular Numbers**
 (copied from archive)
 TODO: include in some form mathlib or figure out how to import it from archive/ --/
lemma inverse_triangle_sum :
  ∀ n, ∑ k in range n, (2 : ℚ) / (k * (k + 1)) = if n = 0 then 0 else 2 - (2 : ℚ) / n :=
begin
  refine sum_range_induction _ _ (if_pos rfl) _,
  rintro (_|n), { rw [if_neg, if_pos]; norm_num },
  simp_rw [if_neg (succ_ne_zero _), succ_eq_add_one],
  have A : (n + 1 + 1 : ℚ) ≠ 0, by { norm_cast, norm_num },
  push_cast,
  field_simp [cast_add_one_ne_zero],
  ring,
end

/-- **Sum of products of consecutive reciprocals** -/
lemma partial_sum_consecutive_reciprocals :
 ∀ n, ∑ k in range n, (1 : ℚ) / (k.succ * (k.succ.succ)) ≤ 1 :=
begin
  intro n,
  rw [← (mul_le_mul_left (zero_lt_two)), mul_sum], swap, { exact rat.nontrivial },
  { have h : ∀ (k : ℕ), k ∈ (range n) →
      2 * ((1 : ℚ) / (k.succ * (k.succ.succ))) = 2 / (k.succ * (k.succ.succ)),
      by { intros k hk, rw [mul_div], rw [mul_one (2 : ℚ)] },
    rw sum_congr rfl h,
    have h₁ := inverse_triangle_sum n.succ,
    rw sum_range_succ' at h₁,
    norm_num at *,
    rw h₁,
    rw [sub_le_self_iff],
    refine (le_div_iff _).mpr (_),
    { exact (cast_lt.mpr n.succ_pos), },
    { rw [zero_mul], exact zero_le_two, } },
 end


/-!
 ### Part 1
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/

/--
A sequence of real numbers `an n` has limit `a`, if and only if only if the shifted
sequence given by `an n.succ` has the limit `a`.
-/
lemma tendsto_succ (an : ℕ → ℝ) (a : ℝ) : tendsto an at_top (𝓝 a) ↔
  tendsto (λ n : ℕ, (an n.succ)) at_top (𝓝 a) :=
begin
  nth_rewrite_rhs 0 ← tendsto_map'_iff,
  have h : map succ at_top = at_top :=
  begin
    rw map_at_top_eq_of_gc pred 1,
    { exact @succ_le_succ, },
    { intros a b hb,
      cases (exists_eq_succ_of_ne_zero (one_le_iff_ne_zero.mp hb)) with d hd,
      rw [hd, pred_succ],
      exact succ_le_succ_iff, },
    { intros b hb,
      cases (exists_eq_succ_of_ne_zero (one_le_iff_ne_zero.mp hb)) with d hd,
      rw hd,
      rw pred_succ, },
  end,
  rw h,
end

/--
Define `an n` as $\frac{n!}{\sqrt{2n}/(\frac{n}{e})^n.
Stirling's formula states that this sequence has limit $\sqrt(π)$.
-/
noncomputable def an (n : ℕ) : ℝ := (n.factorial : ℝ) / ((sqrt(2 * n) * ((n / (exp 1))) ^ n))

/--The function `log(1 + x) - log(1 - x)` has a power series expansion with k-th term
2 x^(2k+1)/(2k+1), valid for `|x| < 1`. -/
lemma log_sum_plus_minus (x : ℝ) (hx : |x| < 1) : has_sum (λ k : ℕ,
  (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (x ^ (2 * k + 1))) (log (1 + x) - log(1 - x)) :=
begin
 have h₁, from has_sum_pow_div_log_of_abs_lt_1 hx,
  have h₂, from has_sum_pow_div_log_of_abs_lt_1 (eq.trans_lt (abs_neg x) hx),
  replace h₂ := (has_sum_mul_left_iff  (λ h:(-1 = (0:ℝ)), one_ne_zero (neg_eq_zero.mp h))).mp h₂,
  rw [neg_one_mul, neg_neg, sub_neg_eq_add 1 x] at h₂,
  have h₃, from has_sum.add h₂ h₁,
  rw [tactic.ring.add_neg_eq_sub] at h₃,
  let term := (λ n :ℕ, ((-1) * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) + (x ^ (n + 1) / ((n : ℝ) + 1)))),
  let two_mul := (λ (n : ℕ), (2 * n)),
  rw ←function.injective.has_sum_iff (mul_right_injective two_pos) _ at h₃,
  { suffices h_term_eq_goal :
    (term ∘ two_mul) = (λ k : ℕ, 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k  + 1)),
    by {rw h_term_eq_goal at h₃, exact h₃},
    apply funext,
    intro n,
    rw [function.comp_app],
    dsimp only [two_mul, term],
    rw odd.neg_pow (⟨n, rfl⟩ : odd (2 * n + 1)) x,
    rw [neg_one_mul, neg_div, neg_neg, cast_mul, cast_two],
    ring },
  { intros m hm,
    rw [range_two_mul, set.mem_set_of_eq] at hm,
    rw [even.neg_pow (even_succ.mpr hm), succ_eq_add_one, neg_one_mul, neg_add_self] },
end

/--
For any natural number `n ≠ 0`, we have the identity
`log((n + 1) / n) = log(1 + 1 / (2*n + 1)) - log(1 - 1/(2*n + 1))`.
-/
lemma aux_log (n : ℕ) (hn : n ≠ 0) :
  log (n.succ / n) = log (1 + 1 / (2 * n + 1)) - log (1 - 1 / (2 * n + 1)) :=
begin
  have : (2 : ℝ) * n + 1 ≠ 0, by { norm_cast, exact (2 * n).succ_ne_zero, },
  rw ← log_div,
  suffices h, from congr_arg log h,
    all_goals {field_simp [cast_ne_zero.mpr]}, /- all_goals prevents using brackets here -/
  { ring },
  { norm_cast, exact succ_ne_zero (2 * n + 1) },
end

/--
For any natural number `n`, the expression `log((n + 1) / n)` has the series expansion
$\sum_{k=0}^{\infty} frac{2}{2k+1}(\frac{1}{2n+1})^{2k+1}$.
-/
lemma power_series_ln (n : ℕ) (hn : n ≠ 0) : has_sum (λ (k : ℕ),
  (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * ((1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)))
  (log ((n.succ : ℝ) / (n : ℝ))) :=
 begin
  have h₀ : (0 < n), from zero_lt_iff.mpr hn,
  have h₁ : |1 / (2 * (n : ℝ) + 1)| < 1, by --in library??
  { rw [abs_of_pos, div_lt_one]; norm_cast,
    any_goals {linarith}, /- can not use brackets for single goal, bc of any_goals -/
    { exact div_pos one_pos (cast_pos.mpr (2 * n).succ_pos) }, },
  rw aux_log n (hn),
  exact log_sum_plus_minus (1 / (2 * (n : ℝ) + 1)) h₁,
 end

/--
`bn n` is log of `an n`.
-/
noncomputable def bn (n : ℕ) : ℝ := log (an n)

/--
For each natural number `n ≠ 0`, we have $0<\sqrt{2n}$.
-/
lemma zero_lt_sqrt_two_n (n : ℕ) (hn : n ≠ 0) : 0 < sqrt (2 * (n : ℝ)) :=
   real.sqrt_pos.mpr (mul_pos two_pos (cast_pos.mpr (zero_lt_iff.mpr hn)))

/--
We have the expression `bn (n+1)` = log(n + 1)! - 1 / 2 * log(2 * n) - n * log ((n + 1) / e)
-/
lemma bn_formula (n : ℕ): bn n.succ = (log (n.succ.factorial : ℝ)) -
  1 / (2 : ℝ) * (log (2 * (n.succ : ℝ))) - (n.succ : ℝ) * log ((n.succ : ℝ) / (exp 1)) :=
begin
  have h3, from (lt_iff_le_and_ne.mp (zero_lt_sqrt_two_n n.succ (succ_ne_zero n))).right,
  have h4 : 0 ≠ ((n.succ : ℝ) / exp 1) ^ n.succ, from
    ne_of_lt ((pow_pos (div_pos (cast_pos.mpr n.succ_pos ) (exp_pos 1)) (n.succ))),
  rw [bn, an, log_div, log_mul, sqrt_eq_rpow, log_rpow, log_pow],
  { linarith },
  { exact (zero_lt_mul_left zero_lt_two).mpr (cast_lt.mpr n.succ_pos),},
  { exact h3.symm, },
  { exact h4.symm, },
  { exact cast_ne_zero.mpr n.succ.factorial_ne_zero, },
  { apply (mul_ne_zero h3.symm h4.symm), },
end


/--
The sequence `bn (m + 1) - bn (m + 2)` has the series expansion
   `∑ 1 / (2 * (k + 1) + 1) * (1 / 2 * (m + 1) + 1)^(2 * (k + 1))`
-/
lemma bn_diff_has_sum (m : ℕ) :
  has_sum (λ (k : ℕ), (1 : ℝ) / (2 * k.succ + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ (k.succ))
  ((bn m.succ) - (bn m.succ.succ)) :=
begin
  have hx : ∀ (n : ℕ), (bn n.succ) - (bn n.succ.succ) =
    ((n.succ : ℝ) + 1 / (2 : ℝ)) * log(((n.succ.succ) : ℝ) / (n.succ : ℝ)) - 1 :=
  begin
    intro n,
    have h_reorder : ∀ {a b c d e f : ℝ}, a - 1 / (2 : ℝ) * b - c - (d - 1 / (2 : ℝ) * e - f) =
      (a - d) - 1 / (2 : ℝ) * (b - e) - (c - f),
    by {intros, ring_nf},
    rw [bn_formula, bn_formula, h_reorder],
    repeat {rw [log_div, factorial_succ]},
    push_cast,
    repeat {rw log_mul},
    rw log_exp,
    ring_nf,
    all_goals {norm_cast},
    all_goals {try {refine mul_ne_zero _ _}, try {exact succ_ne_zero _}},
    any_goals {exact factorial_ne_zero n},
    any_goals {exact exp_ne_zero 1},
  end,
  have h_sum₀, from power_series_ln m.succ (succ_ne_zero m),
  have h_nonzero : (m.succ : ℝ) + 1 / (2 : ℝ) ≠ 0,
  by {rw cast_succ, field_simp, norm_cast, linarith}, --there has to be a better way...
  rw has_sum_mul_left_iff h_nonzero at h_sum₀,
  have h_inner : ∀ (b : ℕ) , (((m.succ : ℝ) + 1 / 2) * (2 * (1 / (2 * (b : ℝ) + 1)) *
      (1 / (2 * (m.succ : ℝ) + 1)) ^ (2 * b + 1)))
      = (1 : ℝ) / (2 * (b : ℝ) + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ b :=
  begin
    intro b,
    rw [← pow_mul, pow_add],
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
    { exact ᾰ },
    { refine sum_congr rfl _, intros k hk, exact h_inner k },
  end,
  have h_sum : tendsto
    (λ (n : ℕ), ∑ (k : ℕ) in range n.succ,
    (λ (b : ℕ), 1 / (2 * (b : ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ b) k)
    at_top (𝓝 (((m.succ : ℝ) + 1 / 2) * log ((m.succ.succ : ℝ) / (m.succ : ℝ)))) :=
    (has_sum.tendsto_sum_nat h_sum₁).comp (tendsto_add_at_top_nat 1),
  have split_zero : ∀ (n : ℕ), ∑ (k : ℕ) in range n.succ,
    1 / (2 * (k : ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ k =
    (∑ (k : ℕ) in range n,
    1 / (2 * (k.succ : ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ k.succ) + 1 := by
    { intro n,
      rw sum_range_succ' (λ (k : ℕ),
        1 / (2 * (k : ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ k) n,
      dsimp only [], --beta reduce functions
      rw [pow_zero, mul_one, cast_zero, mul_zero, zero_add, div_one] },
  replace h_sum := tendsto.congr split_zero h_sum,
  replace h_sum := tendsto.add_const (-1) h_sum,
  simp only [add_neg_cancel_right] at h_sum, --beta reduce and rw?
  rw tactic.ring.add_neg_eq_sub _ (1 : ℝ) at h_sum,
  rw ← hx at h_sum,
  exact (summable.has_sum_iff_tendsto_nat
    ((summable_nat_add_iff 1).mpr (has_sum.summable h_sum₁))).mpr h_sum,
end

/-- The sequence `bn` is monotone decreasing -/
lemma bn_antitone : ∀ (n m : ℕ), n ≤ m → bn m.succ ≤ bn n.succ :=
begin
  apply antitone_nat_of_succ_le,
  intro n,
  refine sub_nonneg.mp _,
  rw ← succ_eq_add_one,
  refine has_sum.nonneg _ (bn_diff_has_sum n),
  norm_num,
  simp only [one_div],
  intro m,
  refine mul_nonneg _ _,
  all_goals {refine inv_nonneg.mpr _, norm_cast, exact (zero_le _)},
end

/--
We have the bound  `bn n - bn (n+1) ≤ 1/(2n+1)^2* 1/(1-(1/2n+1)^2)`.
-/
lemma bn_diff_le_geo_sum : ∀ (n : ℕ),
  bn n.succ - bn n.succ.succ ≤ (1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2) :=
begin
  intro n,
  have g : has_sum (λ (k : ℕ), ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ)
    ((1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2)) :=
  begin
    have h_pow_succ := λ (k : ℕ),
      symm (pow_succ ((1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2) k),
    have h_nonneg : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2),
    by { rw [cast_succ, one_div, inv_pow₀, inv_nonneg], norm_cast, exact zero_le', },
    have hlt : ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) < 1, by
    { simp only [cast_succ, one_div, inv_pow₀],
      refine inv_lt_one _,
      norm_cast,
      simp only [nat.one_lt_pow_iff, ne.def, zero_eq_bit0, nat.one_ne_zero, not_false_iff,
        lt_add_iff_pos_left, canonically_ordered_comm_semiring.mul_pos, succ_pos', and_self], },
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
      { exact ᾰ },
      { refine sum_congr rfl _, intros k hk, exact h_pow_succ k },
    end,
    norm_num,
    exact h_geom'',
  end,
  have hab :
    ∀ (k : ℕ), (1 / (2 * (k.succ : ℝ) + 1)) * ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ ≤
    ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ :=
  begin
    intro k,
    have h_zero_le : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ, by
    { simp [cast_succ, one_div, inv_pow₀, inv_nonneg], norm_cast, exact zero_le', },
    have h_left : 1 / (2 * (k.succ : ℝ) + 1) ≤ 1, by
    { simp only [cast_succ, one_div],
      refine inv_le_one _,
      norm_cast,
      exact (le_add_iff_nonneg_left 1).mpr zero_le', },
    exact mul_le_of_le_one_left h_zero_le h_left,
  end,
  exact has_sum_le hab (bn_diff_has_sum n) g,
end

/--
We have the bound  `bn n - bn (n+1)` ≤ 1/(4n(n+1))
-/
lemma bn_sub_bn_succ : ∀ (n : ℕ),
bn n.succ - bn n.succ.succ ≤ 1 / (4 * n.succ * n.succ.succ) :=
begin
  intro n,
  have h₁ : 0 < 4 * (n.succ : ℝ) * (n.succ.succ : ℝ), by
  { norm_cast, simp only [canonically_ordered_comm_semiring.mul_pos, succ_pos', and_self], },
  have h₂ : 0 < 1 - (1 / (2 * (n.succ : ℝ) + 1)) ^ 2 :=
  begin
    refine sub_pos.mpr _,
    refine (sq_lt_one_iff _).mpr _,
    { rw one_div,
      refine inv_nonneg.mpr _,
      norm_cast,
      exact zero_le (2 * succ n + 1) },
    { refine (div_lt_one _).mpr _,
      all_goals {norm_cast},
      linarith,
      refine lt_add_of_pos_left 1 ((1 : ℕ).succ_mul_pos (succ_pos n)), },
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

/-- For any `n`, we have `bn 1 - bn n ≤ 1/4` -/
lemma bn_bounded_aux : ∀ (n : ℕ), bn 1 - bn n.succ ≤ 1 / 4 :=
begin
  let bn' : (ℕ → ℝ) := λ (k : ℕ), bn k.succ,
  intro n,
  calc
  bn 1 - bn n.succ = bn' 0 - bn' n : rfl
   ... = ∑ k in range n, (bn' k - bn' (k + 1))          : by rw ← (sum_range_sub' bn' n)
   ... = ∑ k in range n, (bn k.succ - bn k.succ.succ)   : rfl
   ... ≤ ∑ k in range n, 1 / (4 * k.succ * k.succ.succ) : sum_le_sum (λ k, λ hk, bn_sub_bn_succ k)
   ... = ∑ k in range n, (1 / 4) * (1 / (k.succ * k.succ.succ)) :
   begin
     have hi : ∀ (k : ℕ), (1 : ℝ) / (4 * k.succ * k.succ.succ) =
      (1 / 4) * (1 / (k.succ * k.succ.succ)) :=
     begin
       intro k,
       norm_cast,
       field_simp,
       simp only [one_div, inv_inj],
       ring_nf,
     end,
    refine sum_congr rfl (λ k, λ hk, hi k),
   end
   ... = 1 / 4 * ∑ k in range n, 1 / (k.succ * k.succ.succ) : by rw mul_sum
   ... ≤ 1 / 4 * 1 :
   begin
     refine (mul_le_mul_left _).mpr _,
     { exact div_pos one_pos four_pos },
     { convert rat.cast_le.mpr (partial_sum_consecutive_reciprocals n),
       rw rat_cast_sum,
       push_cast,
       exact rat.cast_one.symm },
   end
   ... = 1 / 4 : by rw mul_one,
end

/-- The sequence `bn` is bounded below by `3/4 - 1/2 * log 2`  for `n ≥ 1`. -/
lemma bn_bounded_by_constant : ∀ (n : ℕ), 3 / (4 : ℝ) - 1 / 2 * log 2 ≤ bn n.succ :=
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

/-- The sequence `bn` is bounded below. -/
lemma bn_has_lower_bound : (lower_bounds (set.range (λ (k : ℕ), bn k.succ))).nonempty :=
begin
   use 3 / (4 : ℝ) - 1 / 2 * log 2,
   intros,
   rw lower_bounds,
   rw [set.mem_set_of_eq],
   simp only [set.mem_range, forall_apply_eq_imp_iff', forall_exists_index],
   exact bn_bounded_by_constant,
end

/--
Any sequence `bn` of real numbers that is monotone decreasing and bounded below has
a limit in the real numbers.
-/
lemma monotone_convergence (bn : ℕ → ℝ) (h_sd : ∀ (n m : ℕ), n ≤ m → bn m ≤ bn n)
  (h_bounded : (lower_bounds (set.range bn)).nonempty) : ∃ (m : ℝ), tendsto bn at_top (𝓝 m) :=
begin
 use Inf (set.range bn),
 exact tendsto_at_top_is_glb h_sd (real.is_glb_Inf (set.range bn)
   (set.range_nonempty bn) h_bounded),
end

/-- The sequence `an` is positive for `n > 0`  -/
lemma an'_pos : ∀ (n : ℕ), 0 < an n.succ :=
 (λ n, div_pos (cast_pos.mpr (factorial_pos n.succ))
    (mul_pos ((real.sqrt_pos).mpr (mul_pos two_pos (cast_pos.mpr (succ_pos n))))
    (pow_pos (div_pos (cast_pos.mpr (succ_pos n)) (exp_pos 1)) n.succ)))

/--
The sequence `an` has the explicit lower bound exp (3/4 - 1/2 * log 2)
-/
lemma an'_bounded_by_pos_constant : ∀ (n : ℕ), exp (3 / (4 : ℝ) - 1 / 2 * log 2) ≤ an n.succ :=
begin
  intro n,
  rw ← (le_log_iff_exp_le (an'_pos n)),
  exact bn_bounded_by_constant n,
end

/-- The sequence `an` is monotone decreasing -/
lemma an'_antitone : ∀ (n m : ℕ), n ≤ m → an m.succ ≤ an n.succ :=
  (λ n, λ m, λ h, (log_le_log (an'_pos m) (an'_pos n)).mp (bn_antitone n m h))

/-- The sequence `an` has a lower bound -/
lemma an'_has_lower_bound : (lower_bounds (set.range (λ (k : ℕ), an k.succ))).nonempty :=
begin
   use exp (3 / (4 : ℝ) - 1 / 2 * log 2),
   intros,
   rw lower_bounds,
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact an'_bounded_by_pos_constant,
end

/-- The sequence `an` converges to a real number -/
lemma an_has_limit_a : ∃ (a : ℝ), tendsto (λ (n : ℕ), an n) at_top (𝓝 a) :=
begin
  have ha := monotone_convergence (λ (k : ℕ), an k.succ) an'_antitone an'_has_lower_bound,
  cases ha with x hx,
  rw ← tendsto_succ an x at hx,
  use x,
  exact hx,
end

/-- The limit `a` of the sequence `an` satisfies `0 < a` -/
lemma an_has_pos_limit_a : ∃ (a : ℝ), 0 < a ∧ tendsto (λ (n : ℕ), an n) at_top (𝓝 a) :=
begin
  have h := an_has_limit_a,
  cases h with a ha,
  use a,
  split,
  { let an' : ℕ → ℝ := λ n, an n.succ,
    rw tendsto_succ an a at ha,
    have e_lower_bound : exp (3 / (4 : ℝ) - 1 / 2 * log 2) ∈ lower_bounds (set.range an') :=
    begin
      intros x hx,
      rw [set.mem_range] at hx,
      cases hx with k hk,
      rw ← hk,
      exact an'_bounded_by_pos_constant k,
    end,
    exact gt_of_ge_of_gt ((le_is_glb_iff (is_glb_of_tendsto_at_top an'_antitone ha)).mpr
      e_lower_bound) (3 / 4 - 1 / 2 * log 2).exp_pos },
  { exact ha },
end

/-!
 ### Part 2
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_2
-/

/--
Define `wallis_inside_prod n` as `2 * n / (2 * n - 1) * 2 * n/(2 * n + 1)`.
This is the term appearing inside the Wallis product
-/
noncomputable def wallis_inside_prod (n : ℕ) : ℝ :=
  (((2 : ℝ) * n) / (2 * n - 1)) * ((2 * n) / (2 * n + 1))

/--
We can shift the indexing in a product.
 -/
lemma aux1 (k : ℕ) : ∏ i in range k, (wallis_inside_prod (1 + i)) =
    ∏ i in Ico 1 k.succ, wallis_inside_prod i :=
begin
  rw [range_eq_Ico],
  rw prod_Ico_add wallis_inside_prod 0 k 1,
end

/-- The wallis product $\prod_{n=1}^k \frac{2n}{(2n-1}\frac{2n}{2n+1}$
  converges to `π/2` as `k → ∞` -/
lemma equality1: tendsto (λ (k : ℕ), ∏ i in Ico 1 k.succ, wallis_inside_prod i) at_top (𝓝 (π/2)) :=
begin
  rw ← tendsto_congr (aux1),
  have h : ∀ i,
  wallis_inside_prod (1 + i) = (((2 : ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3)) :=
  begin
    intro i,
    rw [wallis_inside_prod, cast_add, cast_one],
    have hl : (2 : ℝ) * (1 + (i : ℝ)) / (2 * (1 + (i : ℝ)) - 1) =
      (2 * (i : ℝ) + 2) / (2 * (i : ℝ) + 1), by
    { refine congr (congr_arg has_div.div _) _; ring_nf, },
    have hr : (2 : ℝ) * (1 + (i : ℝ)) / (2 * (1 + (i : ℝ)) + 1) =
      ((2 * (i : ℝ) + 2) / (2 * (i : ℝ) + 3)), by
    { refine congr (congr_arg has_div.div _) _; ring_nf, },
    rw [hl, hr],
  end,
  have h_prod : ∀ k, ∏ (m : ℕ) in range k, wallis_inside_prod (1 + m) =
    ∏ (m : ℕ) in range k, (((2 : ℝ) * m + 2) / (2 * m + 1)) * ((2 * m + 2) / (2 * m + 3)), by
  { intro k, rw prod_congr (refl (range k)) _, intros x hx, exact h x, },
  rw tendsto_congr h_prod,
  exact tendsto_prod_pi_div_two,
end

/--
For any `n : ℕ` satisfying `n > 0` and any `r : ℝ`, we have
r * (2 * n)^2 / ((2 * n + 1) * (2 * n - 1)^2) =
r / (2* (n - 1) + 1) * 2 * n / (2 * n- 1) * 2n /(2n + 1)
-/
lemma aux2 (r : ℝ) (n : ℕ) : 1 / (((2 * n.succ + 1) : ℕ) : ℝ) *
  (r * (((((2 * n.succ) ^ 2) : ℕ ): ℝ) / ((((2 * n.succ) : ℕ) : ℝ) - 1) ^ 2)) =
  (1 / (((2 * n + 1) : ℕ) : ℝ) * r) * ((((2 * n.succ) : ℕ) : ℝ) / ((((2 * n.succ) : ℕ) : ℝ) - 1) *
  ((((2 * n.succ) : ℕ) : ℝ) / (((2 * n.succ + 1) : ℕ) : ℝ))) :=
begin
  by_cases h : r = 0,
  { repeat {rw h},
    rw [zero_mul, mul_zero, mul_zero, zero_mul] },
  { have : 2 * ((n : ℝ) + 1) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero _},
    have : 2 * (n : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero _},
    have : 2 * ((n : ℝ) + 1) - 1 ≠ 0, by {ring_nf, norm_cast, exact succ_ne_zero _},
    field_simp,
    ring_nf },
end

/-- For any `n : ℕ`, we have
$\prod_{k=1}^n \frac{2n}{2n-1}\frac{2n}{2n+1}
  = \frac{1}{2n+1} \prod_{k=1}^n \frac{(2k)^2}{(2*k-1)^2}$
-/
lemma equation3 (n : ℕ): ∏ k in Ico 1 n.succ, wallis_inside_prod k =
  (1 : ℝ) / (2 * n + 1) * ∏ k in Ico 1 n.succ, ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 :=
begin
  induction n with d hd,
  { simp only [Ico_self, prod_empty, cast_zero, mul_zero,
    zero_add, div_one, mul_one] },
  { rw [succ_eq_add_one],
    norm_cast,
    rw [prod_Ico_succ_top, hd, wallis_inside_prod],
    symmetry,
    rw prod_Ico_succ_top,
    {norm_cast,rw aux2, },
    all_goals {apply zero_lt_succ} },
end

/--  For any `n : ℕ` with `n ≠ 0`, we have
`(2* n)^2 / (2*n - 1)^2 = (2 * n)^2 / (2 * n - 1)^2*(2*n)^2 / (2*n)^2` -/
lemma equation4 (n : ℕ) (hn : n ≠ 0) : ((2 : ℝ) * n) ^ 2 / (2 * n - 1) ^ 2 =
  ((2 : ℝ) * n) ^ 2 / (2 * n - 1) ^ 2 * ((2 * n) ^ 2 / (2 * n) ^ 2) :=
begin
  have h : ((2 : ℝ) * n) ^ 2 ≠ 0,
    from pow_ne_zero 2 (mul_ne_zero two_ne_zero (cast_ne_zero.mpr hn)),
  rw div_self h, rw mul_one,
end

/--
For any `n : ℕ`, we have
1/(2n+1)*∏_{k=1}^n (2k)^2/(2k-1)^2 = 1/(2n+1) ∏_{k=1}^n (2k)^2/(2k-1)^2 * (2k)^2/(2k)^2.
-/
lemma equation4' (n : ℕ) : 1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 =
  1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 * ((2 * k) ^ 2 / (2 * k) ^ 2) :=
begin
  rw prod_congr rfl,
  intros d hd,
  rw ← equation4,
  rw mem_Ico at hd,
  exact one_le_iff_ne_zero.mp hd.left,
end

/--
For any `n : ℕ`, we have
(2n)^2/(2n-1)^2 * (2n)^2/(2n)^2 = 2^4 * n^4 / ((2n-1)*(2n))^2.
-/
lemma equation5 (n : ℕ) : ((2 : ℝ) * n) ^ 2 / (2 * n - 1) ^ 2 * ((2 * n) ^ 2 / (2 * n) ^ 2) =
  ((2 : ℝ) ^ 4 * n ^ 4) / ((2 * n - 1) * (2 * n)) ^ 2 :=
begin
  cases n with d hd,
  { rw [cast_zero, mul_zero, zero_pow two_pos, zero_div, zero_mul],
    rw [zero_pow four_pos, mul_zero, zero_div], },
  { have : 2 * (d.succ : ℝ) - 1 ≠ 0, by
    { rw [cast_succ], ring_nf, norm_cast, exact succ_ne_zero (2*d), },
    have : (d.succ : ℝ) ≠ 0 := cast_ne_zero.mpr (succ_ne_zero d),
    field_simp,
    ring_nf, },
end

/--
For any `n : ℕ`, we have
1/(2n+1) ∏_{k=1}^n (2k)^2/(2k-1)^2*(2k)^2/(2k)^2 = 1/(2n+1) ∏_{k=1}^n 2^4 k^4/ ((2k-1)(2k))^2.
-/
lemma equation5' (n : ℕ) : 1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 * ((2 * k) ^ 2 / (2 * k) ^ 2) =
  1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) ^ 4 * k ^ 4) / ((2 * k - 1) * (2 * k)) ^ 2 :=
begin
  rw prod_congr rfl, intros d hd, rw ← equation5,
end

/--
For any `n : ℕ`, we have
1/(2n+1) ∏_{k=1}^n 2^4 k^4/ ((2k-1)(2k))^2 = 2^(4n)*(n!)^4/((2n)!^2 *(2n+1)) .
-/
lemma equation6 (n : ℕ) : 1 / ((2 : ℝ) * n + 1) * ∏ (k : ℕ) in Ico 1 n.succ,
  (2 : ℝ) ^ 4 * k ^ 4 / ((2 * k - 1) * (2 * k)) ^ 2 =
  (2 : ℝ) ^ (4 * n) * n.factorial ^ 4 / ((2 * n).factorial ^ 2 * (2 * n + 1)) :=
begin
  induction n with d hd,
  { rw [Ico_self, prod_empty, cast_zero, mul_zero, mul_zero, mul_zero, factorial_zero],
    rw [zero_add, pow_zero, cast_one, one_pow, one_pow, mul_one, mul_one] },
  { replace hd := congr_arg (has_mul.mul (2* (d : ℝ) + 1)) hd,
    have : 2 * (d : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2 * d)},
    rw [← mul_assoc, mul_one_div_cancel this, one_mul] at hd,
    rw [prod_Ico_succ_top (succ_le_succ (zero_le d)), hd, mul_succ 2],
    repeat {rw factorial_succ},
    have : 2 * (d : ℝ) + 1 + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2 * d + 1)},
    have : 2 * (d.succ : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2 * d.succ)},
    have : 2 * ((d : ℝ) + 1) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2 * (d + 1))},
    have : ((2 * d).factorial : ℝ) ≠ 0, by {norm_cast, exact factorial_ne_zero (2 * d)},
    have : 2 * ((d : ℝ) + 1) - 1 ≠ 0, by {ring_nf, norm_cast, exact succ_ne_zero (2 * d)},
    have : 2 * ((d : ℝ) + 1) ≠ 0, by {norm_cast, exact mul_ne_zero two_ne_zero (succ_ne_zero d)},
    field_simp,
    rw [mul_succ 4 d, pow_add _ (4 * d) 4],
    ring_nf }, --this one might be quite heavy without "generalize" before
end

/-- For `n : ℕ`, define `wn n` as `2^(4*n) * n!^4 / ((2*n)!^2 * (2*n + 1))` -/
noncomputable def wn (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (4 * n) * (n.factorial) ^ 4) / ((((2 * n).factorial) ^ 2) * (2 * (n : ℝ) + 1))

/-- The sequence `wn n`converges to `π/2`-/
lemma wallis_consequence : tendsto (λ (n : ℕ), wn n) at_top (𝓝 (π/2)) :=
begin
  convert equality1,
  simp only [equation6, equation3, wn, equation4', equation5', wn],
end

/--
If a sequence  `an` has a limit `A`, then the subsequence of only even terms has the same limit
-/
lemma sub_seq_tendsto {an : ℕ → ℝ} {A : ℝ} (h : tendsto an at_top (𝓝 A)) :
  tendsto (λ (n : ℕ), an (2 * n)) at_top (𝓝 A) :=
h.comp (tendsto_id.const_mul_at_top' two_pos)

/-- For `n : ℕ`, define `cn n` as √2n * (n/e)^(4n) *2^(4n) / ((√4n (2n/e)^(2n))^2 * (2n+1)) -/
noncomputable def cn (n : ℕ) : ℝ := ((sqrt (2 * n) * ((n / (exp 1)) ^ n)) ^ 4) * 2 ^ (4 * n) /
  (((sqrt (4 * n) * (((2 * n) / (exp 1))) ^ (2 * n))) ^ 2 * (2 * n + 1))

/-- For any `n :ℕ`, we have `cn n` = n/(2n+1)-/
lemma rest_cancel (n : ℕ) : (n : ℝ) / (2 * n + 1) = cn n :=
begin
  rw cn,
  have h₀ : 4 = 2 * 2, by refl,
  rw [mul_pow, mul_pow, h₀, pow_mul, sq_sqrt, sq_sqrt],
  { cases n,
    { rw [cast_zero, zero_div, mul_zero, zero_pow, zero_mul, zero_mul, zero_div],
    exact two_pos },
    { have h₁ : 2 * (n.succ : ℝ) + 1 ≠ 0,
    by { norm_cast, exact succ_ne_zero (2*n.succ) },
    have h₂ : exp 1 ≠ 0, from exp_ne_zero 1,
    have h₃ : (n.succ : ℝ) ≠ 0, by exact cast_ne_zero.mpr (succ_ne_zero n),
    field_simp,
    repeat {rw [← pow_mul]},
    rw [← h₀, mul_assoc 2 n.succ 2, mul_left_comm 2 n.succ 2, ← h₀],
    rw [mul_pow (2 : ℝ) _ (n.succ * 4), mul_comm 4 n.succ],
    ring_nf }, },
  all_goals {norm_cast, linarith},
end

/-- The sequence `cn n` has limit 1/2-/
lemma rest_has_limit_one_half : tendsto (λ (n : ℕ), cn n) at_top (𝓝 (1 / 2)) :=
begin
  apply (tendsto.congr rest_cancel),
  have h : tendsto (λ (k : ℕ), (((k : ℝ) / (2 * (k : ℝ) + 1))⁻¹))
    at_top (𝓝 (((1 : ℝ) / 2))⁻¹) :=
  begin
    have hsucc : tendsto (λ (k : ℕ), (((k.succ : ℝ) / (2 * (k.succ : ℝ) + 1))⁻¹)) at_top
      (𝓝 (((1 : ℝ) / 2))⁻¹) :=
    begin
      have hx : ∀ (k : ℕ), (2 : ℝ) + k.succ⁻¹ = ((k.succ : ℝ) / (2 * k.succ + 1))⁻¹, by
      { intro k, have hxne : (k.succ : ℝ) ≠ 0 := nonzero_of_invertible (k.succ : ℝ), field_simp, },
      simp only [one_div, inv_inv],
      apply (tendsto.congr hx),
      have g := tendsto.add tendsto_const_nhds ((tendsto_add_at_top_iff_nat 1).mpr
        (tendsto_inverse_at_top_nhds_0_nat)),
      rw [add_zero] at g,
      exact g,
    end,
    exact (tendsto_add_at_top_iff_nat 1).mp hsucc,
  end,
  have h2: ((1 : ℝ) / 2)⁻¹ ≠ 0, by
    simp only [one_div, inv_inv, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff],
  convert tendsto.inv₀ h h2,
  { simp only [inv_inv, one_div] },
  { rw inv_inv },
end

/--
Suppose the sequence `an` (defined above) has a nonzero limit `a ≠ 0`.
Then the sequence 1/ (an n)^2 has the limit 1/a^2.
-/
lemma an_aux3 (a : ℝ) (hane : a ≠ 0) (ha : tendsto (λ (n : ℕ), an n) at_top (𝓝 a)) :
  tendsto (λ (n : ℕ), (1 / (an n)) ^ 2) at_top (𝓝 ((1 / a) ^ 2)) :=
begin
 convert tendsto.pow (tendsto.congr (λ n, (one_div (an n)).symm) (tendsto.inv₀ ha hane)) 2,
 rw [one_div],
end

/-- For any `n ≠ 0`, we have the identity (an n)^4/ (an (2n))^2 * (cn n) = wn n. -/
lemma expand_in_limit (n : ℕ) (hn : n ≠ 0) : (an n) ^ 4 * (1 / (an (2 * n))) ^ 2 * cn n = wn n :=
begin
  rw [an, an, cn, wn],
  have : (4 : ℝ) = (2 : ℝ) * 2, by norm_cast,
  rw this,
  rw [cast_mul 2 n, cast_two, ←mul_assoc],
  rw sqrt_mul (mul_self_nonneg 2) (n : ℝ),
  rw sqrt_mul_self zero_le_two,
  have h₀ : (n : ℝ) ≠ 0, from cast_ne_zero.mpr hn,
  have h₁ : sqrt (2 * (n : ℝ)) ≠ 0, from (ne_of_lt (zero_lt_sqrt_two_n n hn)).symm,
  have h₂ : (exp 1) ≠ 0, from exp_ne_zero 1,
  have h₃ : ((2 * n).factorial : ℝ) ≠ 0, from cast_ne_zero.mpr (factorial_ne_zero (2 * n)),
  have h₄ : sqrt (n : ℝ) ≠ 0, from sqrt_ne_zero'.mpr (cast_pos.mpr (zero_lt_iff.mpr hn)),
  have h₅ : (((2 * n) : ℕ) : ℝ) ≠ 0,
    from cast_ne_zero.mpr (mul_ne_zero two_ne_zero hn),
  have h₆ : sqrt (4 * (n : ℝ)) ≠ 0,
    from sqrt_ne_zero'.mpr (mul_pos four_pos (cast_pos.mpr (zero_lt_iff.mpr hn))),
  have h₇ : 2 * (n : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2*n)},
  field_simp,
  ring_nf,
end

/-- For any `n : ℕ`, we have the identity (an n+1)^4/ (an (2(n+1)))^2 * (cn n+1) = wn n+1. -/
lemma expand_in_limit' (n : ℕ) :
  (an n.succ) ^ 4 * (1 / (an (2 * n.succ))) ^ 2 * cn n.succ = wn n.succ :=
  expand_in_limit n.succ (succ_ne_zero n)

/--
Suppose the sequence `an` (defined above) has the limit `a ≠ 0`.
Then the sequence `wn` has limit `a^2/2`
-/
lemma second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : tendsto an at_top (𝓝 a)) :
  tendsto wn at_top (𝓝 (a ^ 2 / 2)):=
begin
  rw tendsto_succ wn (a ^ 2 / 2),
  apply tendsto.congr expand_in_limit',
  let qn := λ (n : ℕ), an n ^ 4 * (1 / an (2 * n)) ^ 2 * cn n,
  have hqn :
    ∀ (n : ℕ), qn n.succ = an n.succ ^ 4 * (1 / an (2 * n.succ)) ^ 2 * cn n.succ := by tauto,
  apply tendsto.congr hqn,
  rw ←tendsto_succ qn (a ^ 2 / 2),
  have has : tendsto (λ (n : ℕ), an n ^ 4 * (1 / an (2 * n)) ^ 2) at_top (𝓝 (a ^ 2)) :=
  begin
    convert tendsto.mul (tendsto.pow ha 4) (sub_seq_tendsto (an_aux3 a hane ha)),
    field_simp,
    ring_nf,
  end,
  convert tendsto.mul has rest_has_limit_one_half,
  rw [one_div, div_eq_mul_inv],
end

/-- Stirling's Formula: The sequence `an n` = n!/ √2n (n/e)^n has limit sqrt π-/
lemma an_has_limit_sqrt_pi : tendsto (λ (n : ℕ), an n) at_top (𝓝 (sqrt π)) :=
begin
  have ha := an_has_pos_limit_a,
  cases ha with a ha,
  cases ha with hapos halimit,
  have hπ : π / 2 = a ^ 2 / 2 := tendsto_nhds_unique wallis_consequence
    (second_wallis_limit a (ne_of_gt hapos) halimit),
  field_simp at hπ,
  rw ← (sq_sqrt (le_of_lt pi_pos)) at hπ,
  have h := (sq_eq_sq (sqrt_nonneg π) (le_of_lt hapos)).mp hπ,
  convert halimit,
end

end stirling
