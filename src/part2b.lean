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

import part2

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat

example (a b : (ℕ →  ℝ)) (A B : ℝ)
(hA: tendsto (λ (k : ℕ), a k) at_top (𝓝 (A)))
(hB: tendsto (λ (k : ℕ), b k) at_top (𝓝 (B))) :
tendsto (λ (k : ℕ), a k * (b k)) at_top (𝓝 (A * B)) :=
begin
 exact tendsto.mul hA hB,
end

example: tendsto (λ (x : ℕ), ((x : ℝ))⁻¹) at_top (𝓝 0)
:=tendsto_inverse_at_top_nhds_0_nat



example: tendsto (λ (x : ℕ), ((2 : ℝ))) at_top (𝓝 2):=
 tendsto_const_nhds

example (a : ℕ → ℝ) (A : ℝ)
(h: tendsto (λ (k : ℕ), a (k + 1)) at_top (𝓝 (A))):
tendsto (λ (k : ℕ), a (k)) at_top (𝓝 (A)) :=
begin
  exact (tendsto_add_at_top_iff_nat 1).mp h,
end



lemma tendsto_inv' (a : ℕ → ℝ) (A : ℝ) (hA: 0≠A)
 (h: tendsto (λ (k : ℕ), a k) at_top (𝓝 (A))) :
  (tendsto (λ (k : ℕ), (a k)⁻¹) at_top (𝓝 (A⁻¹))) :=
begin
  exact tendsto.inv₀ h (ne.symm hA),
end

lemma const_tendsto (a : ℕ → ℝ) (A : ℝ):
 tendsto (λ (k : ℕ), (0 : ℝ)) at_top (𝓝 (0)) :=
begin
  simp only [tendsto_const_nhds],
end


example (x y :ℝ) (hx: x≠0) (hy: y≠0):
 x*y ≠ 0 := mul_ne_zero hx hy


example (x y : ℝ) (hx: 0 ≤ x) (hy: 0 ≤ y) (hxy: x^2 = y^2):
x = y:=
begin
  exact (sq_eq_sq hx hy).mp hxy,
end

-- part 2b of https://proofwiki.org/wiki/Stirling%27s_Formula


lemma sub_seq_tendsto {an : ℕ → ℝ} {A : ℝ}
 (h: tendsto an at_top (𝓝 A)):
 tendsto (λ (n : ℕ), an (2*n)) at_top (𝓝 A) :=
h.comp (tendsto_id.const_mul_at_top' two_pos)


noncomputable def cn (n : ℕ) : ℝ  :=
 ((real.sqrt(2*n)*((n/(exp 1))^n))^4) * 2^(4*n) /
 (((real.sqrt(4*n)*(((2*n)/(exp 1)))^(2*n)))^2 * (2*n + 1))

lemma rest_cancel (n : ℕ):
 (n : ℝ) / (2*n + 1) = cn n :=
 begin
   rw cn,
   cases n,
   simp only [cast_zero, mul_zero, zero_div, real.sqrt_zero, zero_mul, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero,
  not_false_iff],
   have h1: 2 * (n.succ : ℝ) + 1 ≠ 0 :=
   begin
     norm_cast,
     rw ←succ_eq_add_one,
     exact succ_ne_zero (2*n.succ),
   end,
  -- mmh, do we have to do `cases n` here and for h3 as well?
   have h2: (sqrt (4 * (n.succ : ℝ)) * (2 * ↑n.succ / exp 1) ^ (2 * n.succ)) ^ 2 *
   (2 * ↑n.succ + 1) ≠ 0 :=
   begin
     norm_cast,
     simp only [cast_mul, cast_bit0, cast_one, cast_succ, sqrt_mul, zero_le_bit0, zero_le_one, div_pow, cast_add, mul_eq_zero,
  pow_eq_zero_iff, succ_pos', real.sqrt_eq_zero, bit0_eq_zero, one_ne_zero, false_or, div_eq_zero_iff,
  canonically_ordered_comm_semiring.mul_pos, and_self],
     norm_num,
     push_neg,
     split,
     split,
     rw sqrt_ne_zero _,
     norm_cast,
     exact succ_ne_zero n,
     norm_cast,
     exact zero_le (n + 1),
     split,
     norm_cast,
     exact succ_ne_zero n,
     exact (1:ℝ).exp_ne_zero,
     norm_cast,
     exact (2 * (n + 1)).succ_ne_zero,
   end,
   field_simp,
   have h3: (exp 1 ^ n.succ) ^ 4 * ((sqrt 4 * sqrt ↑n.succ *
   (2 * ↑n.succ) ^ (2 * n.succ)) ^ 2 * (2 * ↑n.succ + 1)) ≠ 0 :=
   begin
     simp only [cast_succ, ne.def, mul_eq_zero, pow_eq_zero_iff, succ_pos', real.sqrt_eq_zero, zero_le_bit0, zero_le_one,
  bit0_eq_zero, one_ne_zero, false_or, canonically_ordered_comm_semiring.mul_pos, and_self],
    push_neg,
    split,
    exact (1:ℝ).exp_ne_zero,
    split,
    split,
    rw sqrt_ne_zero _,
    norm_cast,
    exact succ_ne_zero n,
    norm_cast,
    exact zero_le (n + 1),
    norm_cast,
    exact succ_ne_zero n,
    norm_cast,
    exact (2 * (n + 1)).succ_ne_zero,
   end,
   field_simp,

   norm_cast,
   rw add_comm n 1,
   rw ←succ_eq_one_add n,
   generalize:  n.succ = m,
   ring,
   have h4: real.sqrt m ^ 4 = m^2 :=
   begin
     rw sqrt_eq_rpow,
     have h:= (rpow_mul (cast_nonneg m) (1/2) 4),
     norm_cast at h,
     rw ←h,
     ring,
     norm_cast,
   end,
   have h5: real.sqrt ↑m ^ 2 = m := sq_sqrt (cast_nonneg m),
   have h6: real.sqrt 2 ^ 4 = sqrt 4 ^ 2 :=
   begin
     rw sq_sqrt,
     {
     have h4eq2mul2: 4 = 2 * 2 := by linarith,
     have h:= rpow_mul ((2:ℝ).sqrt_nonneg) 2 2,
     norm_cast at h,
     rw h4eq2mul2,
     rw h,
     rw sq_sqrt,
     ring,
     simp only [zero_le_bit0, zero_le_one],
     },
     norm_cast,
     exact cast_nonneg 4,
   end,
   have h7: (exp 1 ^ m) ^ 4 = (exp 1 ^ (2*m)) ^ 2 :=
   begin
     repeat {rw ←pow_mul},
     rw mul_assoc 2,
     rw mul_comm 2,
     rw mul_assoc,
     ring,
   end,
   have h8: ((m:ℝ) ^ m) ^ 4 * ↑(2 ^ (4 * m)) =
    ↑((2 * m) ^ (2 * m)) ^ 2 :=
   begin
    norm_cast,
    repeat {rw mul_pow},
    repeat {rw ←pow_mul},
    rw mul_assoc 2,
    rw mul_comm 2,
    rw mul_assoc,
    norm_num,
    simp only [mul_comm],
   end,
   rw [h4, h5, h6, h7, ←h8],
   field_simp,
   linarith,
 end

lemma rest_has_limit_one_half: tendsto
(λ (n:ℕ), cn n) at_top (𝓝 (1/2)) :=
begin
 apply (tendsto.congr rest_cancel),
 have h: tendsto (λ (x : ℕ), (((x:ℝ )/ (2 * ↑x + 1))⁻¹))
 at_top (𝓝 (((1:ℝ ) / 2))⁻¹):=
 begin
  have hsucc: tendsto (λ (x : ℕ), (((x.succ:ℝ )/ (2 * ↑x.succ + 1))⁻¹))
  at_top (𝓝 (((1:ℝ ) / 2))⁻¹):=
  begin
    -- this indirection (considering the succ) is taken,
    -- becuase otherwise we would have a hard time
    -- proving hxne
    have hx: ∀ (x:ℕ), (2:ℝ) + x.succ⁻¹ = ((x.succ : ℝ) / (2 * x.succ + 1))⁻¹  :=
    begin
      intro x,
      have hxne: (x.succ : ℝ) ≠ 0 :=
      begin
        exact nonzero_of_invertible ↑(succ x),
      end,
      field_simp,
    end,
    simp only [one_div, inv_inv],
    apply (tendsto.congr (hx)),
    have h_right: tendsto (λ (x : ℕ), ((x : ℝ))⁻¹) at_top (𝓝 0)
      :=tendsto_inverse_at_top_nhds_0_nat,
    have h_left: tendsto (λ (x : ℕ), ((2 : ℝ))) at_top (𝓝 2):=
  tendsto_const_nhds,
    have g:= tendsto.add h_left ((tendsto_add_at_top_iff_nat 1).mpr h_right),
    simp only [add_zero] at g,
    exact g,
  end,
  exact (tendsto_add_at_top_iff_nat 1).mp hsucc,
 end,
 have h2: ((1:ℝ )/2)⁻¹ ≠ 0 :=
 begin
   simp only [one_div, inv_inv, ne.def, bit0_eq_zero,
   one_ne_zero, not_false_iff],
 end,
 have g:= tendsto.inv₀ h h2,
 simp only [inv_inv, one_div] at g,
 simp only [one_div],
 exact g,
end

lemma an_aux1 (a: ℝ) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
tendsto  (λ (n: ℕ), (an n)^4) at_top (𝓝 (a^4)) :=
begin
 exact tendsto.pow ha 4,
end



lemma an_aux2 (a: ℝ) (hane: a≠0) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
tendsto (λ (n : ℕ),  (an n)⁻¹) at_top (𝓝  ((a)⁻¹)) :=
begin
  exact tendsto.inv₀ ha hane,
end

lemma an_aux3 (a: ℝ) (hane: a≠0) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
tendsto  (λ (n: ℕ), (1/(an n))^(2)) at_top (𝓝 ((1/a)^(2))) :=
begin
 have h := an_aux2 a hane ha,
 rw ←one_div at h,
 have hainv : ∀ n:ℕ, (an n)⁻¹ = 1/(an n) :=
 begin
   intro n,
   rw ←one_div,
 end,
 have h_congr := tendsto.congr hainv h,
 apply tendsto.pow h_congr 2,
end

lemma an_aux4 (a: ℝ) (hane: a≠0) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
tendsto  (λ (n: ℕ), (1/(an (2*n)))^(2)) at_top (𝓝 ((1/a)^(2))):=
begin
  have h := an_aux3 a hane ha,
  exact sub_seq_tendsto h,
end

-- added the assumption hn. Without that the statement is false (I think).
-- With the new assumption, the lemma below does not work anymore...
lemma expand_in_limit (n : ℕ) (hn: n ≠ 0):
 (an n)^4 * (1/(an (2 * n)))^(2) * cn n = wn n:=
begin
  rw an,
  rw an,
  rw cn,
  rw wn,
  norm_cast,
  have h1:  sqrt (2 * (n : ℝ)) * (↑n / exp 1) ^ n ≠ 0 :=
  begin
    simp only [sqrt_mul', cast_nonneg, div_pow, ne.def, mul_eq_zero, real.sqrt_eq_zero, zero_le_bit0, zero_le_one, bit0_eq_zero,
  one_ne_zero, cast_eq_zero, false_or, div_eq_zero_iff],
    push_neg,
    split,
    exact hn,
    split,
    norm_cast,
    exact ne_of_gt (pow_pos (zero_lt_iff.mpr hn) n),
    exact ne_of_gt (pow_pos (1:ℝ).exp_pos n),
  end,
  have hn2: 0 < 2*n :=
    begin
      simp only [canonically_ordered_comm_semiring.mul_pos, succ_pos', true_and],
      exact zero_lt_iff.mpr hn,
    end,
  have h2 : (((2 * n).factorial) :ℝ) / (sqrt ↑(2 * (2 * n))
    * (↑(2 * n) / exp 1) ^ (2 * n)) ≠ 0 :=
  begin
    simp only [cast_mul, cast_bit0, cast_one, zero_le_mul_left, zero_lt_bit0, zero_lt_one, cast_nonneg, div_pow, ne.def,
  div_eq_zero_iff, cast_eq_zero, mul_eq_zero, real.sqrt_eq_zero, bit0_eq_zero, one_ne_zero, false_or],
    push_neg,
    split,
    exact factorial_ne_zero (2*n),
    split,
    exact hn,
    split,
    norm_cast,
    exact ne_of_gt (pow_pos hn2 (2*n)),
    exact ne_of_gt (pow_pos (1:ℝ).exp_pos (2*n)),
  end,
  have h3: real.sqrt ↑(2 * (2 * n)) * (↑(2 * n) / exp 1) ^ (2 * n) ≠ 0 :=
  begin
    norm_cast,
    simp only [cast_mul, cast_bit0, cast_one, zero_le_mul_left, zero_lt_bit0, zero_lt_one, cast_nonneg, div_pow, mul_eq_zero,
  real.sqrt_eq_zero, bit0_eq_zero, one_ne_zero, cast_eq_zero, false_or, div_eq_zero_iff],
    push_neg,
    split,
    exact hn,
    split,
    norm_cast,
    exact ne_of_gt (pow_pos hn2 (2*n)),
    exact ne_of_gt (pow_pos (1:ℝ).exp_pos (2*n)),
  end,
  have h4 : (((2 * n).factorial) :ℝ) ^ 2 *  (2 * n + 1) ≠ 0 :=
  begin
    refine mul_ne_zero _ _,
    norm_cast,
    simp only [pow_eq_zero_iff, succ_pos'],
    exact factorial_ne_zero (2*n),
    norm_cast,
    exact succ_ne_zero (2*n),
  end,
  have h5: (real.sqrt 2 * sqrt ↑n * ↑n ^ n) ^ 4 *
   ((((2 * n).factorial)) * exp 1 ^ (2 * n)) ^ 2 *
   ((exp 1 ^ n) ^ 4 * ((sqrt 4 * sqrt ↑n *
   (2 * ↑n) ^ (2 * n)) ^ 2 * (2*n + 1))) ≠ 0 :=
   begin
    norm_cast,
    simp only [cast_pow, cast_mul, cast_bit0, cast_one, cast_add, mul_eq_zero, pow_eq_zero_iff, succ_pos', real.sqrt_eq_zero,
  zero_le_bit0, zero_le_one, bit0_eq_zero, one_ne_zero, cast_nonneg, cast_eq_zero, false_or],
    push_neg,
    split,
    split,
    split,
    exact hn,
    norm_cast,
    exact ne_of_gt (pow_pos (zero_lt_iff.mpr hn) n),
    split,
    exact factorial_ne_zero (2*n),
    exact ne_of_gt (pow_pos (1:ℝ).exp_pos (2*n)),
    split,
    exact ne_of_gt (pow_pos (1:ℝ).exp_pos (n)),
    split,
    split,
    exact hn,
    norm_cast,
    exact ne_of_gt (pow_pos hn2 (2*n)),
    norm_cast,
    exact succ_ne_zero (2*n),
   end,
  field_simp,
  ring,
  have h6: real.sqrt 4 ^ 2 = 4 := by simp only [sq_sqrt, zero_le_bit0, zero_le_one],
  have h7: real.sqrt 2 ^ 8 = 2 ^ 4 :=
  begin
    have h: 8 = 2 * 4 := by linarith,
    rw h,
    rw pow_mul,
    have g: (0 : ℝ) ≤ 2 := zero_le_two,
    rw sq_sqrt g,
  end,
  have h8: real.sqrt 2 ^ 4 = 2 ^ 2 :=
  begin
    have h: 4 = 2 * 2 := by linarith,
    rw h,
    rw pow_mul,
    have g: (0 : ℝ) ≤ 2 := zero_le_two,
    rw sq_sqrt g,
  end,
  rw [h6, h7, h8],
  ring,
end

lemma expand_in_limit' (n : ℕ):
 (an n.succ)^4 * (1/(an (2 * n.succ)))^(2) * cn n.succ = wn n.succ:=
 begin
   have hn: n.succ ≠ 0 := succ_ne_zero n,
   exact expand_in_limit n.succ hn,
 end

lemma second_wallis_limit (a: ℝ) (hane: a≠0) (ha: tendsto
an at_top (𝓝  a)):
tendsto wn at_top (𝓝 (a^2/2)):=
begin
  rw tendsto_succ wn (a^2/2),
  apply tendsto.congr expand_in_limit',
  let qn := λ (x:ℕ), an x ^ 4 * (1 / an (2 * x)) ^ 2 * cn x,
  have hqn: ∀  (x:ℕ), qn x.succ = an x.succ ^ 4 * (1 / an (2 * x.succ)) ^ 2 * cn x.succ := by tauto,
  apply tendsto.congr hqn,
  rw ←tendsto_succ qn (a^2/2),
  have hcn := rest_has_limit_one_half,
  have has : tendsto (λ (n : ℕ),
  an n ^ 4 * (1 / an (2*n)) ^ 2) at_top (𝓝 (a ^ 2)) :=
  begin
    have haright := an_aux4 a hane ha,
    have haleft := an_aux1 a ha,
    have g := tendsto.mul  haleft haright,
    have a_pow : a ^ 4 * (1 / a) ^ 2  = a ^ 2 :=
    begin
      field_simp,
      ring,
    end,
    rw a_pow at g,
    exact g,
  end,
  have h := tendsto.mul has hcn,
  rw one_div (2:ℝ) at h,
  rw div_eq_mul_inv _,
  exact h,
end

lemma pi_and_a (a: ℝ) (hane: a ≠ 0) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
π/2 = a^2/2 :=
begin
  have h := second_wallis_limit a hane ha,
  have g := wallis_consequence,
  exact tendsto_nhds_unique g h,
end

lemma an_has_limit_sqrt_pi: tendsto
(λ (n : ℕ),  an n) at_top (𝓝 (sqrt π)) :=
begin
  have ha:= an_has_pos_limit_a,
  cases ha with a ha,
  cases ha with hapos halimit,
  have hπ: π/2 = a^2/2 := pi_and_a a _ halimit,
  field_simp at hπ,
  have zero_le_pi: 0 ≤ π :=
  begin
    exact le_of_lt pi_pos,
  end,
  rw ←(sq_sqrt zero_le_pi) at hπ,
  have h:= (sq_eq_sq (sqrt_nonneg π) (le_of_lt hapos)).mp hπ,
  rw ←h at halimit,
  exact halimit,
  exact ne_of_gt hapos,
end
