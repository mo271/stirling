import tactic
import analysis.special_functions.log
import data.fintype.basic
import algebra.big_operators.basic
import algebra.big_operators.intervals
import data.finset.sum
import data.real.basic
import topology.instances.real
import topology.instances.ennreal
import order.filter
import analysis.special_functions.pow
import analysis.special_functions.integrals
import data.real.pi.wallis

import part1b

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat

-- part 2 of https://proofwiki.org/wiki/Stirling%27s_Formula

noncomputable def wallis_inside_prod (n : ℕ) : ℝ :=
  (((2 : ℝ) * n) / (2 * n - 1)) * ((2 * n) / (2 * n + 1))

--uses wallis_inside_prod
lemma aux1 (k : ℕ) : ∏ i in range k, (wallis_inside_prod (1 + i)) =
    ∏ i in Ico 1 k.succ, wallis_inside_prod i :=
begin
  rw [range_eq_Ico],
  rw prod_Ico_add wallis_inside_prod 0 k 1,
end

--uses wallis_inside_prod, aux1,
lemma equality1: tendsto (λ (k : ℕ), ∏ i in Ico 1 k.succ, wallis_inside_prod i) at_top (𝓝 (π/2)) :=
begin
  rw ← tendsto_congr (aux1),
  have h : ∀ i,
  wallis_inside_prod (1 + i) = (((2 : ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3)) :=
  begin
    simp [wallis_inside_prod],
    intro i,
    have hl: (2 : ℝ) * (1 + (i : ℝ)) / (2 * (1 + (i : ℝ)) - 1) =
      (2 * (i : ℝ) + 2) / (2 * (i : ℝ) + 1) :=
    begin
      refine congr (congr_arg has_div.div _) _,
      ring,
      ring,
    end,
    have hr: ((2 : ℝ) * (1 + (i : ℝ)) / (2 * (1 + (i : ℝ)) + 1)) = ((2 * (i : ℝ) + 2) / (2 * (i : ℝ) + 3)) :=
    begin
      refine congr (congr_arg has_div.div _) _,
      ring,
      ring,
    end,
    rw [hl],
    rw [hr],
  end,
  have h_prod : ∀ k, ∏ (i : ℕ) in range k, wallis_inside_prod (1 + i) =
    ∏ (i : ℕ) in range k, (((2 : ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3)) :=
  begin
    intro k,
    rw prod_congr _ _,
    refl,
    intros x hx,
    exact h x,
  end,
  rw tendsto_congr h_prod,
  exact tendsto_prod_pi_div_two,
end

--uses nothing?
lemma aux2 (r : ℝ) (d : ℕ) : 1 / ((2 * d.succ + 1) : ℝ) *
  (r * ((((2 * d.succ) ^ 2) : ℝ) / (((2 * d.succ) - 1) : ℝ) ^ 2)) =
  (1 / ((2 * d + 1) : ℝ) * r) * (((2 * d.succ) : ℝ) / (((2 * d.succ) : ℝ) - 1) *
  (((2 * d.succ) : ℝ) / ((2 * d.succ + 1) : ℝ))) :=
begin
  by_cases h : r = 0,
  repeat {rw h},
  simp only [zero_mul, mul_zero],
  have : 2 * ((d : ℝ) + 1) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero _},
  have : 2 * (d : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero _},
  have : 2 * ((d : ℝ) + 1) - 1 ≠ 0, by {ring_nf, norm_cast, exact succ_ne_zero _},
  field_simp,
  ring_nf,
end

--uses wallis_insise_prod, aux2
lemma equation3 (n : ℕ):  ∏ k in Ico 1 n.succ, wallis_inside_prod k =
    (1 : ℝ) / (2 * n + 1) * ∏ k in Ico 1 n.succ, ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 :=
begin
  induction n with d hd,
  simp only [Ico_self, prod_empty, cast_zero, mul_zero,
  zero_add, div_one, mul_one],
  rw succ_eq_add_one,
  norm_cast,
  rw prod_Ico_succ_top,
  rw hd,
  rw wallis_inside_prod,
  symmetry,
  rw prod_Ico_succ_top,
  {norm_cast,rw aux2,},
  apply zero_lt_succ,
  apply zero_lt_succ,
end

--uses nothing?
lemma equation4 (k : ℕ) (hk : k ≠ 0) : ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 =
  ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 * ((2 * k) ^ 2 / (2 * k) ^ 2) :=
begin
  have h : (((2 : ℝ) * k) ^ 2 / (2 * k) ^ 2) = 1 :=
  begin
    have hk2 : ((2 : ℝ) * k) ^ 2 ≠ 0 :=
    begin
      simp only [ne.def, pow_eq_zero_iff, succ_pos',
       mul_eq_zero, bit0_eq_zero, one_ne_zero, cast_eq_zero,
       false_or],
      exact hk,
    end,
    rw div_eq_inv_mul,
    rw inv_mul_cancel hk2,
  end,
  rw h,
  simp only [mul_one],
end

--uses equation 4
lemma equation4' (n : ℕ) : 1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 =
  1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 * ((2 * k) ^ 2 / (2 * k) ^ 2) :=
begin
  rw prod_congr,
  refl,
  intros d hd,
  rw ←equation4,
  simp only [mem_Ico] at hd,
  cases hd,
  exact one_le_iff_ne_zero.mp hd_left,
end

--uses nothing?
lemma equation5 (k : ℕ) : ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 * ((2 * k) ^ 2 / (2 * k) ^ 2) =
  ((2 : ℝ) ^ 4 * k ^ 4) / (((2 * k - 1) * (2 * k)) ^ 2) :=
begin
 ring_nf,
 simp only [mul_eq_mul_right_iff, pow_eq_zero_iff,
 succ_pos', cast_eq_zero],
 left,
 norm_cast,
 rw mul_pow _ ((2 * k) : ℝ),
 rw mul_comm _ (((2 * k) ^ 2) : ℝ),
 norm_cast,
 repeat {rw mul_assoc},
 rw congr_arg (has_mul.mul (16 : ℝ)) _,
 simp only [cast_pow, cast_mul, cast_bit0, cast_one],
 rw ←mul_inv₀,
end

--uses equation5,
lemma equation5' (n : ℕ) : 1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) * k) ^ 2 / (2 * k - 1) ^ 2 * ((2 * k) ^ 2 / (2 * k) ^ 2) =
  1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
  ((2 : ℝ) ^ 4 * k ^ 4) / (((2 * k - 1) * (2 * k)) ^ 2) :=
begin
  rw prod_congr,
  refl,
  intros d hd,
  rw ←equation5,
end

--uses nothing?
lemma equation6 (n : ℕ) : 1 / ((2 : ℝ) * n + 1) * ∏ (k : ℕ) in Ico 1 n.succ,
  ((2 : ℝ) ^ 4 * k ^ 4) / (((2 * k - 1) * (2 * k)) ^ 2) =
  ((2 : ℝ) ^ (4 * n) * n.factorial ^ 4) / (((2 * n).factorial ^ 2) * (2 * n + 1)) :=
begin
  induction n with d hd,
  simp only [cast_zero, mul_zero, zero_add, Ico_self,
   prod_empty, mul_one, pow_zero, factorial_zero, cast_one,
    one_pow],
  replace hd := congr_arg (has_mul.mul (2*(d:ℝ)+1)) hd,
  have : 2 * (d : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2 * d)},
  rw [← mul_assoc, mul_one_div_cancel this, one_mul] at hd,
  rw prod_Ico_succ_top,
  rw hd,
  rw [mul_succ 2],
  repeat {rw factorial_succ},
  have : (((2 * d + 1 + 1) * ((2 * d + 1) * (2 * d).factorial)) : ℝ) ≠ 0,
    begin
    norm_cast,
    exact mul_ne_zero (succ_ne_zero (2 * d + 1))
      (mul_ne_zero (succ_ne_zero (2 * d)) (factorial_ne_zero (2 * d))),
    end,
  have : (2 * (d.succ : ℝ) + 1) ≠ 0, by {norm_cast, exact succ_ne_zero (2 * d.succ)},
  have : (2 * ((d : ℝ) + 1) + 1) ≠ 0, by {norm_cast, exact succ_ne_zero (2 * (d + 1))},
  have : (((2 * d).factorial) : ℝ) ^ 2 ≠ 0,
    by {norm_cast, exact pow_ne_zero 2 (factorial_ne_zero (2 * d))},
  have : (2 * ((d : ℝ) + 1) - 1) ≠ 0, by {ring_nf, norm_cast, exact succ_ne_zero (2 * d)},
  have : (2 * ((d : ℝ) + 1)) ≠ 0, by {norm_cast, exact (mul_ne_zero two_ne_zero (succ_ne_zero d))},
  field_simp,
  rw [mul_succ 4 d, pow_add _ (4 * d) 4],
  generalize g₀ : d.factorial = x,
  generalize g₁ : (2 * d).factorial = y,
  generalize g₂ : 2 ^ d = z,
  ring_nf,
  exact succ_le_succ (zero_le d),
end

noncomputable def wn (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (4 * n) * (n.factorial) ^ 4) / ((((2 * n).factorial) ^ 2) * (2 * (n : ℝ) + 1))

--uses wn, wallis_inside_prod, equality1, equation3, equation4', equation5', equation6
lemma wallis_consequence: tendsto (λ (n : ℕ), wn n) at_top (𝓝 (π/2)) :=
begin
  have h : tendsto (λ (k : ℕ), ∏ i in Ico 1 k.succ, wallis_inside_prod i) at_top (𝓝 (π/2)) :=
    equality1,
  rw tendsto_congr equation3 at h,
  rw tendsto_congr equation4' at h,
  rw tendsto_congr equation5' at h,
  rw tendsto_congr equation6 at h,
  exact h,
end
