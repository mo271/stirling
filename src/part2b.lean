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





example (x y : ℝ) (hx: 0 ≤ x) (hy: 0 ≤ y) (hxy: x^2 = y^2):
x = y:=
begin
  exact (sq_eq_sq hx hy).mp hxy,
end

-- part 2b of https://proofwiki.org/wiki/Stirling%27s_Formula

lemma sub_seq_tendsto {an : ℕ → ℝ} {A : ℝ}
 (h: tendsto (λ (n : ℕ), an n) at_top (𝓝 (A))):
 tendsto (λ (n : ℕ), an (2*n)) at_top (𝓝 (A)) :=
begin
  sorry,
end

-- is this or something like it not in library?
lemma unique_limit (a : (ℕ → ℝ)) (A B: ℝ)
(hA: tendsto (λ (k : ℕ), a k) at_top (𝓝 (A)))
(hB: tendsto (λ (k : ℕ), a k) at_top (𝓝 (B))) :
A = B :=
begin
  have h: tendsto
  (λ (k : ℕ), a k - (a k)) at_top (𝓝 (A - B)) :=
  begin
    exact tendsto.sub hA hB,
  end,
  simp only [sub_self] at h,
  have hAB: (0 : ℝ) = A - B :=
  begin
    -- how to use tendsto_const_iff here?
    sorry,
  end,
  exact eq_of_sub_eq_zero (symm hAB),
end

noncomputable def cn (n : ℕ) : ℝ  :=
 ((real.sqrt(2*n)*((n/(exp 1))^n))^4) * 2^(4*n) /
 (((real.sqrt(4*n)*(((2*n)/(exp 1)))^(2*n)))^2 * (2*n + 1))

lemma rest_cancel (n : ℕ):
 (n : ℝ) / (2*n + 1) = cn n :=
 begin
   rw cn,
   have h1: 2 * (n : ℝ) + 1 ≠ 0 := by sorry,
   have h2: (sqrt (4 * (n : ℝ)) * (2 * ↑n / exp 1) ^ (2 * n)) ^ 2 * 
   (2 * ↑n + 1) ≠ 0 := by sorry,
   field_simp,
   have h3: (exp 1 ^ n) ^ 4 * ((sqrt 4 * sqrt ↑n * (2 * ↑n) ^ (2 * n)) ^ 2 * (2 * ↑n + 1)) ≠ 0 := by sorry,
   field_simp,
   norm_cast,
   ring,
   have h4: real.sqrt n ^ 4 = n^2 := by sorry,
   have h5: real.sqrt ↑n ^ 2 = n := by sorry,
   have h6: real.sqrt 2 ^ 4 = sqrt 4 ^ 2 := by sorry,
   have h7: (exp 1 ^ n) ^ 4 = (exp 1 ^ (2*n)) ^ 2 := by sorry,
   have h8: ((n:ℝ) ^ n) ^ 4 * ↑(2 ^ (4 * n)) = 
    ↑((2 * n) ^ (2 * n)) ^ 2 := by sorry,
   rw [h4, h5, h6, h7, ←h8],
   field_simp,
   ring,
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

lemma expand_in_limit (n : ℕ):
 (an n)^4 * (1/(an (2 * n)))^(2) * cn n = wn n:=
begin
  rw an,
  rw an,
  rw cn,
  rw wn,
  generalize : (((2 * n).factorial) :ℝ) = x2,
  generalize : (((n).factorial) :ℝ) = x,
  generalize : (2 * (n : ℝ) + 1) = y,
  norm_cast,
  have h1:  sqrt (2 * (n : ℝ)) * (↑n / exp 1) ^ n ≠ 0 := by sorry,
  have h2 : x2 / (sqrt ↑(2 * (2 * n)) * (↑(2 * n) / exp 1) ^ (2 * n)) ≠ 0 := by sorry,
  have h3: real.sqrt ↑(2 * (2 * n)) * (↑(2 * n) / exp 1) ^ (2 * n) ≠ 0 := sorry,
  have h4 : x2 ^ 2 * y ≠ 0 := by sorry,
  have h5: (real.sqrt 2 * sqrt ↑n * ↑n ^ n) ^ 4 * (x2 * exp 1 ^ (2 * n)) ^ 2 *
  ((exp 1 ^ n) ^ 4 * ((sqrt 4 * sqrt ↑n * (2 * ↑n) ^ (2 * n)) ^ 2 * y)) ≠ 0 := by sorry,
  field_simp,
  ring,
  have h6: real.sqrt 4 ^ 2 = 4 := by sorry,
  have h7: real.sqrt 2 ^ 8 = 2 ^ 4 := by sorry,
  have h8: real.sqrt 2 ^ 4 = 2 ^ 2 := by sorry,
  rw [h6, h7, h8],
  ring,
end

lemma second_wallis_limit (a: ℝ) (hane: a≠0) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
tendsto (λ (n : ℕ), wn n) at_top (𝓝 (a^2/2)):=
begin
  apply tendsto.congr expand_in_limit,
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

lemma pi_and_a (a: ℝ) (hane: a≠0) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
π/2 = a^2/2 :=
begin
  have h := second_wallis_limit a hane ha,
  have g := wallis_consequence,
  exact unique_limit wn (π/2) (a^2/2) g h,
end

lemma an_has_limit_sqrt_pi: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  (sqrt π)) :=
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
