import tactic
import analysis.special_functions.log
import order.filter

import data.fintype.basic
import data.finset.sum
import data.real.basic

open real
open filter
open nat

open_locale filter topological_space

-- Is there some more direct way of proving this or
-- even this lemma somewhere in mathlib?
lemma unique_limit (a : (ℕ → ℝ)) (A B: ℝ)
(hA: tendsto (λ (k : ℕ), a k) at_top (𝓝 (A)))
(hB: tendsto (λ (k : ℕ), a k) at_top (𝓝 (B))) :
A = B :=
begin
  exact tendsto_nhds_unique hA hB,
end

lemma sub_seq_tendsto {an : ℕ → ℝ} {A : ℝ}
 (h: tendsto an at_top (𝓝 A)):
 tendsto (λ (n : ℕ), an (2*n)) at_top (𝓝 A) :=
begin
  refine tendsto.comp _ _,
  exact at_top,
  exact h,
  exact tendsto.const_mul_at_top' (two_pos) tendsto_id,
end
