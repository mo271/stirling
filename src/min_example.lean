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


lemma power_series_log_add_one (x:ℝ) (hx: |x| < 1):
tendsto (λ m, ∑ n in range m, (-(1 : ℝ))^(n - 1) * x^n / n)
at_top (𝓝 (log (1 + x))) :=
begin
  sory,
end
