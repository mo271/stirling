import tactic
import topology.instances.nnreal
import data.real.basic
import data.nat.basic
import order.filter
import topology.basic

open real
open filter
open nat

open_locale filter topological_space

example: covariant_class ℝ ℝ (function.swap has_add.add) has_lt.lt 
:= covariant_swap_add_lt_of_covariant_add_lt ℝ

lemma monotone_convergence (a : ℕ → ℝ) (c : ℝ)
(h_strictly_increasing: strict_mono a)
(h_bounded: ∀ (n : ℕ), a n < c):
∃ (b : ℝ), tendsto (λ (n : ℕ),  a n) at_top (𝓝  b) :=
begin
 use (set.range a),
 sorry,
end

