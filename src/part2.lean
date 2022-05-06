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



example (a b : (ℕ →  ℝ)) (h:∀ (k:ℕ), a k = b k ):
tendsto (λ (k : ℕ), a k) at_top (𝓝 (π/2)) ↔ tendsto (λ (k : ℕ),b k) at_top (𝓝 (π/2)):=
begin
 exact tendsto_congr h,
end

example (a b c d :ℝ) (h:a = c) (g : b = d): a / b = c / d:=
begin
  exact congr (congr_arg has_div.div h) g,
end

example (r s t: ℝ) (h: s = t): r * s = r * t :=
begin
  exact congr_arg (has_mul.mul r) (h),
end

-- part 2 of https://proofwiki.org/wiki/Stirling%27s_Formula

noncomputable def wallis_inside_prod (n : ℕ) : ℝ :=
(((2:ℝ) * n) / (2*n - 1)) * ((2 *n)/(2 * n + 1))

lemma aux1 (k : ℕ): ∏ i in range k, (wallis_inside_prod (1 + i)) =
    ∏ i in Ico 1 k.succ,
    (((2:ℝ) * i) / (2*i - 1)) * ((2 * i)/(2 * i + 1)) :=
begin
  rw [range_eq_Ico],
  rw prod_Ico_add wallis_inside_prod 0 k 1,
  simp only [zero_add],
  refl,
end

lemma equality1: tendsto (λ (k : ℕ), ∏ i in Ico 1 k.succ,
    (((2:ℝ) * i) / (2*i - 1)) * ((2 * i)/(2 * i + 1)))
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

lemma wallis_consequence: tendsto (λ (n : ℕ),
((2:ℝ)^(4*n)*(n.factorial)^4)/((((2*n).factorial)^2)*(2*↑n + 1)))
at_top (𝓝 (π/2)) :=
begin
  sorry,
end

lemma an_has_limit_sqrt_pi: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  (sqrt π)) :=
begin
  sorry,
end
