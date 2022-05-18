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

import part1

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat

-- part 2 of https://proofwiki.org/wiki/Stirling%27s_Formula

noncomputable def wallis_inside_prod (n : ℕ) : ℝ :=
(((2:ℝ) * n) / (2*n - 1)) * ((2 *n)/(2 * n + 1))

lemma aux1 (k : ℕ): ∏ i in range k, (wallis_inside_prod (1 + i)) =
    ∏ i in Ico 1 k.succ,
    wallis_inside_prod i :=
begin
  rw [range_eq_Ico],
  rw prod_Ico_add wallis_inside_prod 0 k 1,
end

lemma equality1: tendsto (λ (k : ℕ), ∏ i in Ico 1 k.succ,
   wallis_inside_prod i)
    at_top (𝓝 (π/2)) :=
begin
  rw ←tendsto_congr (aux1),
  have h : ∀ i,
  wallis_inside_prod (1 + i) = (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3)) :=
  begin
    simp [wallis_inside_prod],
    intro i,
    have hl: (2 : ℝ) * (1 + ↑i) / (2 * (1 + ↑i) - 1)
      = (2 * ↑i + 2) / (2 * ↑i + 1) :=
    begin
      refine congr (congr_arg has_div.div _) _,
      ring,
      ring,
    end,
    have hr: ((2 : ℝ) * (1 + ↑i) / (2 * (1 + ↑i) + 1))
     = ((2 * ↑i + 2) / (2 * ↑i + 3)) :=
    begin
      refine congr (congr_arg has_div.div _) _,
      ring,
      ring,
    end,
    rw [hl],
    rw [hr],
  end,
  have h_prod : ∀ k,
  ∏ (i : ℕ) in range k, wallis_inside_prod (1 + i) =
  ∏ (i : ℕ) in range k, (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3)) :=
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


lemma aux2 (r : ℝ) (d : ℕ):
1 / ↑(2 * d.succ + 1) * (
  r
   * (↑((2 * d.succ) ^ 2) / (↑(2 * d.succ) - 1) ^ 2)) =
   (1 / ↑(2 * d + 1) *
   r
   ) * (↑(2 * d.succ) / (↑(2 * d.succ) - 1)
   * (↑(2 * d.succ) / ↑(2 * d.succ + 1)))
 :=
begin
  rw ←mul_assoc _ r _,
  rw mul_comm _ r,
  rw mul_comm _ r,
  rw mul_assoc r _ _,
  rw mul_assoc r _ _,
  rw congr_arg (has_mul.mul r) _,
  repeat {rw succ_eq_add_one},
  repeat {rw mul_add},
  simp only [mul_one, cast_add, cast_mul, cast_bit0,
  cast_one, one_div, cast_pow],
  repeat {rw pow_two},
  repeat {rw ←(add_sub _ _ _)},
  have two_sub_one: (2:ℝ ) - 1 = 1 := by ring,
  rw two_sub_one,
  norm_cast,
  repeat {rw div_eq_inv_mul},
  rw mul_comm (↑(2 * d + 1))⁻¹,
  rw mul_comm _ ↑((2 * d + 2) * (2 * d + 2)),
  rw mul_comm (↑(2 * d + 2 + 1))⁻¹ _,
  rw cast_mul,
  rw mul_comm (↑(2 * d + 1))⁻¹ ↑(2 * d + 2),
  rw mul_comm (↑(2 * d + 2 + 1))⁻¹ _,
  repeat {rw mul_assoc},
  rw congr_arg (has_mul.mul _) _,
  rw mul_comm (↑(2 * d + 1))⁻¹ _,
  repeat {rw mul_assoc},
  rw congr_arg (has_mul.mul _) _,
  rw mul_comm _ (↑(2 * d + 2 + 1))⁻¹,
  repeat {rw mul_assoc},
  rw congr_arg (has_mul.mul _) _,
  simp only [cast_mul, cast_add, cast_bit0, cast_one],
  repeat {rw ←div_eq_inv_mul},
  ring_nf,
  simp only [inv_pow₀, inv_inj],
  ring,
end

lemma equation3 (n : ℕ):  ∏ k in Ico 1 n.succ,
    wallis_inside_prod k =
    (1:ℝ)/(2 * n + 1) * ∏ k in Ico 1 n.succ,
    ((2 : ℝ) * k)^2/(2 * k - 1)^2 :=
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
  {norm_cast,
    rw aux2,
  },
  apply zero_lt_succ,
  apply zero_lt_succ,
end

lemma equation4 (k : ℕ) (hk: k ≠ 0):
((2 : ℝ) * k)^2/(2 * k - 1)^2 =
((2 : ℝ) * k)^2/(2 * k - 1)^2 * ((2*k)^2/(2*k)^2) :=
begin
  have h : (((2:ℝ)*k)^2/(2*k)^2) = 1 :=
  begin
    have hk2 : ((2:ℝ)*k)^2 ≠ 0:=
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

lemma equation4' (n : ℕ):
1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
((2 : ℝ) * k)^2/(2 * k - 1)^2 =
1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
((2 : ℝ) * k)^2/(2 * k - 1)^2 * ((2*k)^2/(2*k)^2) :=
begin
  rw prod_congr,
  refl,
  intros d hd,
  rw ←equation4,
  simp at hd,
  cases hd,
  exact one_le_iff_ne_zero.mp hd_left,
end

lemma equation5 (k : ℕ):
((2 : ℝ) * k)^2/(2 * k - 1)^2 * ((2*k)^2/(2*k)^2) =
((2 : ℝ)^4 * k^4)/(((2*k - 1)*(2*k))^2) :=
begin
 ring_nf,
 simp only [mul_eq_mul_right_iff, pow_eq_zero_iff,
 succ_pos', cast_eq_zero],
 left,
 norm_cast,
 rw mul_pow _ ↑(2 * k),
 rw mul_comm _ (↑(2 * k) ^ 2),
 norm_cast,
 repeat {rw mul_assoc},
 rw congr_arg (has_mul.mul (16 : ℝ)) _,
 simp only [cast_pow, cast_mul, cast_bit0, cast_one],
 rw ←mul_inv₀,
end

lemma equation5' (n : ℕ):
1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
((2 : ℝ) * k)^2/(2 * k - 1)^2 * ((2*k)^2/(2*k)^2) =
1 / (2 * (n : ℝ) + 1) * ∏ k in Ico 1 n.succ,
((2 : ℝ)^4 * k^4)/(((2*k - 1)*(2*k))^2) :=
begin
  rw prod_congr,
  refl,
  intros d hd,
  rw ←equation5,
end

lemma equation6 (n : ℕ):
1/((2 : ℝ) * n + 1) *
∏  (k : ℕ) in Ico 1 n.succ,
((2 : ℝ)^4 * k^4)/(((2*k - 1)*(2*k))^2) =
((2: ℝ)^(4*n) * n.factorial^4)/(((2*n).factorial^2)*(2*n + 1)) :=
begin
  induction n with d hd,
  simp only [cast_zero, mul_zero, zero_add, Ico_self,
   prod_empty, mul_one, pow_zero, factorial_zero, cast_one,
    one_pow],
  rw succ_eq_add_one,
  rw prod_Ico_succ_top,
  rw ←succ_eq_add_one,
  rw ←mul_assoc,
  {let hd' := (congr_arg (has_mul.mul (2 * (d:ℝ) + 1)) hd),
   rw ←mul_assoc at hd',
   have hnezero: (2 * (d:ℝ) + 1) ≠ 0 :=
   begin
     norm_cast,
     apply succ_ne_zero,
   end,
   rw (mul_one_div_cancel hnezero) at hd',
   rw one_mul at hd',
   rw hd',
   simp only [cast_succ, one_div, factorial_succ, cast_mul],
   have hsucc: 2*d.succ = (2*d).succ.succ :=
   begin
     repeat {rw succ_eq_add_one},
     ring,
   end,
   rw hsucc,
   repeat {rw factorial_succ},
   norm_cast,
   generalize : ((d.factorial)) = x,
   have h0: 0 ≠ ((2*d).factorial) :=  ne_of_lt (factorial_pos (2*d)),
   have h1: (2 * ((d:ℝ) + 1) + 1) * (↑((2*d).factorial)^ 2 * (2 * ↑d + 1)) *
      ((2 * (↑d + 1) - 1) * (2 * (↑d + 1))) ^ 2 ≠ 0 :=
   begin
    norm_cast,
    simp only [cast_mul, cast_add, cast_bit0, cast_one, mul_eq_zero,
     pow_eq_zero_iff, succ_pos', cast_eq_zero, bit0_eq_zero, one_ne_zero,
     false_or],
     push_neg,
     split,
     split,
     norm_cast,
     exact succ_ne_zero (2 * (d + 1)),
     norm_cast,
     split,
     exact h0.symm,
     exact succ_ne_zero (2 * d),
     split,
     rw mul_add,
     norm_cast,
     simp only [mul_one, cast_add, cast_mul, cast_bit0, cast_one],
     rw ←add_sub,
     have two_sub_one_eq_one: (2 : ℝ) - 1 = 1 := by linarith,
     rw two_sub_one_eq_one,
     norm_cast,
     exact succ_ne_zero (2*d),
     norm_cast,
     exact succ_ne_zero d,
   end,
   have h2: ((2 * (d:ℝ) + 1 + 1) * ((2 * ↑d + 1) * ((2*d).factorial))) ^ 2 *
    (2 * (↑d + 1) + 1) ≠ 0 :=
   begin
     norm_cast,
     simp only [nat.mul_eq_zero, pow_eq_zero_iff, succ_pos', succ_ne_zero,
     false_or, or_false],
     exact h0.symm,
   end,
   rw succ_eq_add_one,
   field_simp,
   ring_nf,
   repeat {rw pow_mul},
   have h3: (2:ℝ)^4 = 16 := by linarith,
   have h4: (16 : ℝ)^(d + 1) = 16*16^d :=
   begin
     rw pow_succ,
   end,
   rw [h3, h4],
   linarith,
   },
  exact le_add_self,
end

noncomputable def wn (n : ℕ) : ℝ  :=
((2:ℝ)^(4*n)*(n.factorial)^4)/((((2*n).factorial)^2)*(2*↑n + 1))

lemma wallis_consequence: tendsto (λ (n : ℕ),
wn n) at_top (𝓝 (π/2)) :=
begin
  have h: tendsto (λ (k : ℕ), ∏ i in Ico 1 k.succ,
    wallis_inside_prod i)
    at_top (𝓝 (π/2)) := equality1,
  rw tendsto_congr equation3 at h,
  rw tendsto_congr equation4' at h,
  rw tendsto_congr equation5' at h,
  rw tendsto_congr equation6 at h,
  exact h,
end
