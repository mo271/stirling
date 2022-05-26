import tactic
import topology.instances.nnreal
import data.real.basic
import data.nat.basic
import order.filter
import topology.basic

open real
open filter
open nat

open_locale filter
open_locale topological_space

lemma summable_succ {a : ℕ → ℝ} (h: summable a):
summable (λ (n : ℕ), a n.succ) :=
begin
  sorry,
end


