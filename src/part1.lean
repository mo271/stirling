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
open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real 
open finset
open filter
open nat


example (n : ℕ) : 2 ≤ n.succ.succ :=
begin
  rw succ_eq_add_one,
  rw succ_eq_add_one,
  rw add_assoc,
  simp only [le_add_iff_nonneg_left, zero_le'],
end

lemma const_zero: tendsto (λ (n : ℕ) , 0) 
    at_top (𝓝  0) := 
begin
  exact tendsto_const_nhds,
end

lemma one_div_succ: tendsto (λ (n : ℝ) , (n:ℝ )^(-(1:ℝ))) 
    at_top (𝓝  0) := 
begin
  refine tendsto_rpow_neg_at_top _,
  exact one_pos,
end


lemma one_div_succ': tendsto (λ (n : ℕ) , (n:ℝ )^(-(1:ℝ))) 
    at_top (𝓝  0) := 
begin
  norm_cast,
  rw tendsto,
  rw filter.map,
  sorry,
end

-- part 1 of https://proofwiki.org/wiki/Stirling%27s_Formula

noncomputable def an (n : ℕ) : ℝ  := (n.factorial :ℝ ) 
/ ((real.sqrt(2*(n))*((n/(exp 1)))^n)) 

lemma power_series_ln (n : ℕ): tendsto 
(λ (m : ℕ),  (2:ℝ)*(∑ k in range m, 
(((1/(2*↑k + 1))*((1/(2*((↑n + 1))^(2*↑k + 1)))))))) at_top 
(𝓝 (log (↑n.succ / ↑n)) ):=
 begin
  sorry,
 end

noncomputable def bn (n : ℕ) :ℝ := log (an n)

lemma bn_formula (n : ℕ): bn n = (log ↑n.factorial) - 
1/(2:ℝ)*(log (2*↑n)) - ↑n*log (↑n/(exp 1)) :=
begin
  sorry,
end

lemma bn_strictly_decreasing: ∀ (n : ℕ), bn n > bn n.succ :=
begin
  sorry,
end

lemma bn_bounded_below: ∀ (n : ℕ), bn n > 3/(4:ℝ) - 1/2*log 2 :=
begin
  sorry,
end

lemma bn_has_limit_b: ∃ (b : ℝ), tendsto 
(λ (n : ℕ),  bn n)
  at_top (𝓝  b) :=
begin
  sorry,
end 

lemma an_has_limit_a: ∃ (a : ℝ), tendsto 
(λ (n : ℕ),  an n)
  at_top (𝓝  a) :=
begin
  sorry,
end
