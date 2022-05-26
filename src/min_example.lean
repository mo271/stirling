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


example (n b:ℕ ):
0 ≤ 1 / (2 * ((b:ℝ) + 1) + 1) * (1 / ((2 * ((n:ℝ) + 1) + 1) ^ 2) ^ b.succ)
:=
begin
  simp only [one_div],
  refine mul_nonneg _ _,
  all_goals {refine inv_nonneg.mpr _},
  all_goals {norm_cast},
  exact zero_le (2 * (b + 1) + 1),
  exact zero_le (((2 * (n + 1) + 1) ^ 2) ^ succ b),
end

example (n:ℕ): ((n : ℝ)/(n.succ : ℝ)) ≤ 1 :=
begin
  refine (div_le_one _).mpr _,
  norm_cast,
  exact succ_pos n,
  norm_cast,
  exact le_succ n,
end
