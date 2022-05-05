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