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


example (b x: ℕ):
2 * (1 / (2 * ↑b + 1)) * ((x + 1 / 2) * (1 / (2 * x + 1)) ^ (2 * b + 1)) =
  1 / (2 * ↑b + 1) * (1 / (2 * x + 1)) ^ (2 * b)
:=
begin
 
end

