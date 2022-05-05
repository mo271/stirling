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

import part1

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real 
open finset
open filter
open nat


-- part 2 of https://proofwiki.org/wiki/Stirling%27s_Formula

lemma wallis_consequence: tendsto (λ (n : ℕ), 
((2:ℝ)^(4*n)*(n.factorial)^4)/((((2*n).factorial)^2)*(2*↑n + 1))) 
at_top (𝓝 (π/2)) :=
begin
  sorry,
end

lemma an_has_limit_sqrt_pi: tendsto 
(λ (n : ℕ),  an n)
  at_top (𝓝  (sqrt π)) :=
begin
  sorry,
end