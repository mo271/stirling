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
import order.filter.basic
import order.bounded_order
import analysis.special_functions.pow

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums
open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open nat
open filter


lemma inverse_triangle_sum' :
  ∀ (n : ℕ),
  ∑ k in range n, ((1 : ℝ) / (k.succ * (k.succ.succ))) =
  ((n : ℝ) / n.succ) :=
begin
  refine sum_range_induction _ _ _ _,
  simp only [cast_zero, zero_div],
  push_cast,
  intro n,
  have h₀ : ((n : ℝ) + 1) ≠ 0 :=
  begin
    norm_cast,
    rw ←succ_eq_add_one,
    exact succ_ne_zero n,
  end,
  have h₁ : ((n : ℝ) + 1 + 1) ≠ 0 :=
  begin
    norm_cast,
    repeat {rw ←succ_eq_add_one},
    exact succ_ne_zero n.succ,
  end,
  have h₂ : (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) ≠ 0 :=
  begin
    exact mul_ne_zero h₀ h₁,
  end,
  field_simp,
  ring,
end

lemma partial_sum_consecutive_reciprocals:
 ∀ n, ∑ i in range n, (1 : ℝ) / (i.succ * (i.succ.succ)) ≤ 1 :=
 begin
   intro n,
   rw inverse_triangle_sum' n,
   refine (div_le_one _).mpr _,
   norm_cast,
   exact succ_pos n,
   norm_cast,
   exact le_succ n,
 end
