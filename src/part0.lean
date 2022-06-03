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



lemma rat_cast_sum (s : finset ℕ) (f : ℕ → ℚ) :
  ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : ℝ)) :=
  (rat.cast_hom ℝ).map_sum f s
-- @[simp, norm_cast] lemma rat_cast_sum [add_comm_monoid β] [has_one β] (s : finset α) (f : α → ℚ) :
-- ↑(∑ x in s, f x : ℚ) = (∑ x in s, (f x : β)) := by sorry

/-- **Sum of the Reciprocals of the Triangular Numbers** -/
lemma inverse_triangle_sum :
  ∀ n, ∑ k in range n, (2 : ℚ) / (k * (k + 1)) = if n = 0 then 0 else 2 - (2 : ℚ) / n :=
begin
  refine sum_range_induction _ _ (if_pos rfl) _,
  rintro (_|n), { rw [if_neg, if_pos]; norm_num },
  simp_rw [if_neg (nat.succ_ne_zero _), nat.succ_eq_add_one],
  have A : (n + 1 + 1 : ℚ) ≠ 0, by { norm_cast, norm_num },
  push_cast,
  field_simp [nat.cast_add_one_ne_zero],
  ring,
end


--TODO: use /archive/100-theorems-list/42_inverse_triangle_sum.lean and delete lemma above.
lemma partial_sum_consecutive_reciprocals:
 ∀ n, ∑ k in range n, (1 : ℚ) / (k.succ * (k.succ.succ)) ≤ 1 :=
 begin
   intro n,
   rw [←(mul_le_mul_left (zero_lt_two)), mul_sum],
   have h: ∀ (k : ℕ), k ∈ (range n) →
     2*((1 : ℚ) / (k.succ * (k.succ.succ))) = 2 / (k.succ * (k.succ.succ)) :=
   begin
     intros k hk,
     rw [mul_div],
     rw [mul_one (2:ℚ)],
  end,
  rw finset.sum_congr rfl h,
  have h₁ := inverse_triangle_sum n.succ,
  rw sum_range_succ' at h₁,
  norm_num at *,
  rw h₁,
  simp only [sub_le_self_iff],
  refine (le_div_iff _).mpr (_),
  exact (cast_lt.mpr n.succ_pos),
  rw [zero_mul],
  exact zero_le_two,
  exact rat.nontrivial,
 end
