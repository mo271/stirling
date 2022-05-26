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

lemma sub_seq_tendsto {an : ℕ → ℝ} {A : ℝ}
 (h: tendsto an at_top (𝓝 A)):
 tendsto (λ (n : ℕ), an (2*n)) at_top (𝓝 A) :=
h.comp (tendsto_id.const_mul_at_top' two_pos)

lemma sub_seq_tendsto' {an : ℕ → ℝ} {A : ℝ}
 (h: tendsto an at_top (𝓝 A)):
 tendsto (λ (n : ℕ), an (n.succ)) at_top (𝓝 A) :=
 begin
   refine h.comp _,
   exact tendsto_add_at_top_nat 1,
 end



lemma split_zero (m:ℕ): ∀ (n:ℕ), ∑ (i : ℕ) in range (n.succ),
1 / (2 * (i:ℝ) + 1) * ((1 / (2 * ↑(m.succ) + 1)) ^ 2) ^ i =
 (∑ (i : ℕ) in range n,
1 / (2 * (i.succ:ℝ) + 1) * ((1 / (2 * ↑(m.succ) + 1)) ^ 2) ^ i.succ) + 1 :=
begin
  intro n,
  rw sum_range_succ' (λ k:ℕ, 1 / (2 * (k:ℝ) + 1) * ((1 / (2 * ↑(m.succ) + 1)) ^ 2) ^ k)
  n,
  simp only [one_div, cast_succ, inv_pow₀, cast_zero, mul_zero, zero_add, pow_zero,
  inv_one, mul_one, add_left_inj],
end


