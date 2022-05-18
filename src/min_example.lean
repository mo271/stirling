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


lemma tendsto_succ (an : ℕ → ℝ) (a:ℝ) (h: tendsto an at_top (𝓝 a)):
tendsto (λ n : ℕ, (an n.succ)) at_top (𝓝 a) :=
begin
  intro,
  intro,
  simp only [filter.mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage],
  sorry,
end
