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


example (n:ℕ): (n : ℝ) ≤ (n.succ : ℝ) :=
begin
  library_search,
end

example (n:ℕ): ((n : ℝ)/(n.succ : ℝ)) ≤ 1 :=
begin
  refine (div_le_one _).mpr _,
  norm_cast,
  exact succ_pos n,
  norm_cast,
  exact le_succ n,
end
