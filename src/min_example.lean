import tactic
import analysis.special_functions.log
import analysis.special_functions.log_deriv
import data.fintype.basic
import algebra.big_operators.basic
import algebra.big_operators.intervals
import data.finset.sum
import data.real.basic
import topology.instances.real
import topology.instances.ennreal
import order.filter
import order.bounded_order
import analysis.special_functions.pow

open real
open filter
open finset
open nat

open_locale filter
open_locale topological_space
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

example (b: ℕ) (z:ℝ) (hy_pos: z > 0):
 z / (z * ((2 * ↑b + 1) * z ^ (2 * b))) = 1 / ((2 * ↑b + 1) * z ^ (2 * b)) :=
begin
  rw div_mul_right,
  exact ne_of_gt hy_pos,
  sorry,
end

example (a b c: ℝ) (ha: a ≠ 0) (hb: 0 ≠ b) (hab: 0 ≠ b*a): a/(a*b) = (1/b):=
begin
  rw div_mul_right,
end


