import tactic
import analysis.special_functions.log
import data.fintype.basic
import algebra.big_operators.basic
import algebra.big_operators.intervals
import data.finset.sum
import data.real.basic
import topology.instances.real
import topology.instances.ennreal
import order.filter
import analysis.special_functions.pow
open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat


example (n : ℕ) : 2 ≤ n.succ.succ :=
begin
  rw succ_eq_add_one,
  rw succ_eq_add_one,
  rw add_assoc,
  simp only [le_add_iff_nonneg_left, zero_le'],
end

lemma const_zero: tendsto (λ (n : ℕ) , 0)
    at_top (𝓝  0) :=
begin
  exact tendsto_const_nhds,
end

lemma one_div_succ: tendsto (λ (n : ℝ) , (n:ℝ )^(-(1:ℝ)))
    at_top (𝓝  0) :=
begin
  refine tendsto_rpow_neg_at_top _,
  exact one_pos,
end


lemma one_div_succ': tendsto (λ (n : ℕ) , (n:ℝ )^(-(1:ℝ)))
    at_top (𝓝  0) :=
begin
  norm_cast,
  rw tendsto,
  rw filter.map,
  sorry,
end

-- part 1 of https://proofwiki.org/wiki/Stirling%27s_Formula

noncomputable def an (n : ℕ) : ℝ  := (n.factorial :ℝ )
/ ((real.sqrt(2*n)*((n/(exp 1)))^n))

lemma power_series_ln (n : ℕ): tendsto
(λ (m : ℕ),  (2:ℝ)*(∑ k in range m,
(((1/(2*↑k + 1))*((1/(2*((↑n + 1))^(2*↑k + 1)))))))) at_top
(𝓝 (log (↑n.succ / ↑n)) ):=
 begin
  sorry,
 end

noncomputable def bn (n : ℕ) :ℝ := log (an n)

lemma zero_lt_sqrt_two_n (n : ℕ) : (n ≠ 0) → 0 < real.sqrt (2 * ↑n)  :=
begin
exact pow_ne_zero n,
rw zero_lt_mul_left, 
end

lemma test (n : ℕ) : n+1 ≠ 0 :=
begin
library_search,
apply real.sqrt_pos.mpr,
norm_cast,
have hn : 0<n, from zero_lt_iff.mpr hn,
apply mul_pos two_pos ,
assumption,
exact nat.nontrivial,
end

lemma n_div_exp1_pow_gt_zero(n : ℕ) :  (↑n / exp 1) ^ n >0 :=
begin
cases n,
rw pow_zero,
exact one_pos,
have hsucc : n.succ > 0, from nat.succ_pos n,
apply gt_iff_lt.mpr,

apply pow_pos  _ n.succ,
apply div_pos_iff.mpr,
left, split,
norm_cast, rw ←gt_iff_lt,
exact hsucc,
exact (1:ℝ).exp_pos,
end

lemma bn_formula (n : ℕ):(n ≠ 0)→  bn n = (log ↑n.factorial) - 
1/(2:ℝ)*(log (2*↑n)) - ↑n*log (↑n/(exp 1)) :=
begin

have h3, from  (lt_iff_le_and_ne.mp (zero_lt_sqrt_two_n n H)),
have h4, from  (lt_iff_le_and_ne.mp (n_div_exp1_pow_gt_zero n )),

rw [bn, an],
rw [log_div, log_mul],
rw [sqrt_eq_rpow, log_rpow, log_pow],
ring,

rw zero_lt_mul_left, 
norm_cast,
exact zero_lt_iff.mpr H,
exact zero_lt_two,



exact h3.right.symm,

exact h4.right.symm,

norm_cast,
exact (n.factorial_ne_zero),

apply (mul_ne_zero h3.right.symm h4.right.symm),
end


lemma bn_strictly_decreasing: ∀ (n : ℕ), (n ≠ 0) →  bn n > bn n.succ :=
begin
  intros n hn,
  rw bn_formula n hn, rw bn_formula (n+1) n.succ_ne_zero ,
  sorry,
end

lemma test (n : ℕ) : n+1 ≠ 0 :=
begin
library_search,
end

lemma bn_bounded_below: ∀ (n : ℕ), bn n > 3/(4:ℝ) - 1/2*log 2 :=
begin
  sorry,
end

lemma bn_has_limit_b: ∃ (b : ℝ), tendsto
(λ (n : ℕ),  bn n)
  at_top (𝓝  b) :=
begin
  sorry,
end

lemma an_has_limit_a: ∃ (a : ℝ), tendsto
(λ (n : ℕ),  an n)
  at_top (𝓝  a) :=
begin
  sorry,
end

lemma an_has_pos_limit_a: ∃ (a : ℝ), 0 < a ∧ tendsto
(λ (n : ℕ),  an n)
  at_top (𝓝  a) :=
begin
  sorry,
end
