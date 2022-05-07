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

lemma unique_limit (a : (ℕ → ℝ)) (A B: ℝ)
(hA: tendsto (λ (k : ℕ), a k) at_top (𝓝 (A)))
(hB: tendsto (λ (k : ℕ), a k) at_top (𝓝 (B))) :
A = B :=
begin
 sorry,
end

example (x y : ℝ) (hx: 0 ≤ x) (hy: 0 ≤ y) (hxy: x^2 = y^2):
x = y:=
begin
  exact (sq_eq_sq hx hy).mp hxy,
end

-- part 2b of https://proofwiki.org/wiki/Stirling%27s_Formula

noncomputable def cn (n : ℕ) : ℝ  :=
((real.sqrt(2*n)*((n/(exp 1)))^n))^4 * 2^(4*n) /
((sqrt(4*n)*(2*n/(exp 1)^(2*n))^2) * (2*n + 1))

lemma rest_has_limit_one_half: tendsto
(λ (n:ℕ), cn n) at_top (𝓝 (1/2)) :=
begin
 sorry,
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

lemma expand_in_limit (n : ℕ):
 (an n)^4 * (1/(an n))^(2) * cn n = wn n:=
begin
  rw an,
  rw cn,
  rw wn,
  -- do some generalize here?,
  sorry,
end

lemma second_wallis_limit (a: ℝ) (hane: a≠0) (ha: tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a)):
tendsto (λ (n : ℕ), wn n) at_top (𝓝 (a^2/2)):=
begin
  apply tendsto.congr expand_in_limit,
  have hcn := rest_has_limit_one_half,
  have has : tendsto (λ (n : ℕ),
  an n ^ 4 * (1 / an n) ^ 2) at_top (𝓝 (a ^ 2)) :=
  begin
    have haright := an_aux3 a hane ha,
    have haleft := an_aux1 a ha,
    have g := tendsto.mul  haleft haright,
    have a_pow : a ^ 4 * (1 / a) ^ 2  = a ^ 2 :=
    begin
      sorry,
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
  have ha: ∃ (a : ℝ), tendsto
(λ (n : ℕ),  an n) at_top (𝓝  a) := an_has_limit_a,
  cases ha with a ha,
  have hπ: π/2 = a^2/2 := pi_and_a a _  ha,
  field_simp at hπ,
  have zero_le_pi: 0 ≤ π :=
  begin
    sorry,
  end,
  rw ←(sq_sqrt zero_le_pi) at hπ,
  have h:= (sq_eq_sq _ _).mp hπ,
  rw ←h at ha,
  exact ha,
  sorry,
  sorry,
  sorry,
end
