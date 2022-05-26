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

lemma test (a b c : ℝ) (ha: 0≠a) (h: a =b*c): a/b =c :=
begin
  suggest,
end

example (b x: ℕ):
2 * (1 / (2 * (b:ℝ) + 1)) * ((x + 1 / 2) * (1 / (2 * x + 1)) ^ (2 * b + 1)) =
  1 / (2 * (b:ℝ) + 1) * (1 / (2 * x + 1)) ^ (2 * b)
:=
begin
  norm_num,
  field_simp,
  have h₁: 0 ≠  (2 * (b:ℝ) + 1) * (2 * ↑x + 1) ^ (2 * b) := by sorry,
  have h₂: 0 ≠  (2 * (b:ℝ) + 1) * (2 * (2 * ↑x + 1) ^ (2 * b + 1)) := by sorry,
  cancel_denoms,

  sorry,
end

