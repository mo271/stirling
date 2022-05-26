import tactic
import topology.instances.nnreal
import analysis.special_functions.log
import data.real.basic
import data.nat.basic
import data.fintype.basic
import order.filter
import topology.basic
import data.finset.sum

open real
open filter
open nat
open finset

open_locale filter
open_locale big_operators -- notation ∑ for finite sums
open_locale topological_space


example (n k :ℕ ):
1 / (2 * (k.succ:ℝ) + 1) ≤ 1 :=
begin
  simp only [cast_succ, one_div],
  refine inv_le_one _,
  norm_cast,
  simp only [le_add_iff_nonneg_left, zero_le'],
end
