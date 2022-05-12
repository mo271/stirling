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
/ ((real.sqrt(2*(n))*((n/(exp 1)))^n))

lemma power_series_log_add_one (x:ℝ) (hx: |x| < 1):
tendsto (λ m, ∑ n in range m, (-(1 : ℝ))^(n - 1) * x^n / n)
at_top (𝓝 (log (1 + x))) :=
begin
  sorry,
end

lemma aux_log (n : ℕ) (hn: n ≠ 0):
log (n.succ/n) = log (1 + 1 / (2*n + 1)) - log (1 - 1/(2*n +1)):=
begin
  have h₁: (2:ℝ)*n + 1 ≠ 0 :=
  begin
    norm_cast,
    exact succ_ne_zero (2*n),
  end,
  have h₂: (2:ℝ)*n + 1 = (2:ℝ)*n + 1 := by refl,
  calc log (n.succ/n) = log(n.succ) - log(n) :
    log_div (cast_ne_zero.mpr (succ_ne_zero n)) (cast_ne_zero.mpr hn)
  ... = log(n.succ) - log(n) +  log 2 - log 2: by simp only [add_tsub_cancel_right]
  ... = log 2 + log(n.succ) - (log 2 + log n): by linarith
  ... = log 2 + log(n.succ) - log(2*n) :
    by rw log_mul (two_ne_zero) (cast_ne_zero.mpr hn)
  ... = log(2 * n.succ) - log(2*n) :
    by rw log_mul (two_ne_zero) (cast_ne_zero.mpr (succ_ne_zero n))
  ... = log(2*n.succ) - log(2*n) - log (2*n + 1) + log (2*n + 1) : by simp only [sub_add_cancel]
  ... = log(2*n.succ) - log (2*n + 1) - (log (2*n) - log (2*n + 1)) : by linarith
  ... = log ((2*n.succ)/(2*n + 1))  - (log (2*n) - log (2*n + 1))  :
    begin
      rw log_div,
      simp only [cast_succ, ne.def, mul_eq_zero, bit0_eq_zero, one_ne_zero, false_or],
      exact cast_ne_zero.mpr (succ_ne_zero n),
      norm_cast,
      exact succ_ne_zero (2*n),
    end
  ... =  log ((2*n.succ)/(2*n + 1))  - log ((2*n)/(2*n + 1)) :
    begin
      rw ←log_div,
      simp only [ne.def, mul_eq_zero, bit0_eq_zero, one_ne_zero,
      cast_eq_zero, false_or],
      exact hn,
      norm_cast,
      exact succ_ne_zero (2*n),
    end
  ... = log(((2*n + 1) + 1)/(2*n + 1)) - log ((2*n)/(2*n + 1)) :
  begin
     have h: (2 : ℝ)*n.succ =  2*n + 1 + 1 :=
      begin
      rw succ_eq_add_one,
      norm_cast,
      end,
    rw h,
  end
  ... = log(((2*n + 1) + 1)/(2*n + 1)) - log ((2*n + 1 - 1)/(2*n + 1)) :
    by simp only [add_sub_cancel]
  ... = log (1 + 1 / (2*n + 1)) - log ((2*n + 1 - 1)/(2*n + 1))  : _
  ... = log (1 + 1 / (2*n + 1)) - log (1 - 1/(2*n +1)) : _,
  rw add_div _ (1 : ℝ),
  rw (div_eq_one_iff_eq h₁).mpr h₂,
  rw sub_div _ (1 : ℝ),
  rw (div_eq_one_iff_eq h₁).mpr h₂,
end

lemma power_series_ln (n : ℕ): tendsto
(λ (m : ℕ),  (2:ℝ)*(∑ k in range m,
(((1/(2*↑k + 1))*((1/(2*((↑n + 1))^(2*↑k + 1)))))))) at_top
(𝓝 (log (↑n.succ / ↑n)) ):=
 begin
  sorry,
 end

noncomputable def bn (n : ℕ) :ℝ := log (an n)

lemma pow_neq_zero_if (n : ℕ) (x : ℝ) : (x ≠ 0 → x^n ≠ 0) :=
begin
exact pow_ne_zero n,
end

lemma zero_lt_sqrt_two_n (n : ℕ) : (n ≠ 0) → 0 < real.sqrt (2 * ↑n)  :=
begin
intro hn,
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
intro H,
have h3, from  (lt_iff_le_and_ne.mp (zero_lt_sqrt_two_n n H)),
have h4, from  (lt_iff_le_and_ne.mp (n_div_exp1_pow_gt_zero n )),
rw [bn, an, log_div, log_mul, sqrt_eq_rpow, log_rpow, log_pow],
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
  rw bn_formula n hn, rw bn_formula (n+1) n.succ_ne_zero,
  apply sub_pos.mp,
  ring_nf,
  push_cast,
  have hreorder :∀ { a b c d e f : ℝ}, a + (b + ( c + ( d + ( e + f))))
      = (a + d) + (e + b) + (f + c) :=
      begin
        intros,
        ring_nf,
      end,
  rw hreorder,
  
  repeat {rw ←sub_eq_add_neg} ,
  rw ←mul_sub, 
  have hreorder₂ : ∀{x y z : ℝ }, x*(y+1)-z*y = (x-z)*y+x:=
    begin
      intros,
      ring_nf,
    end,
  rw hreorder₂,
  repeat {rw ←log_div},
  simp only [factorial_succ],
  rw div_mul_eq_div_mul_one_div _ 2 (n:ℝ),
  
  
  --simp only [cast_mul, cast_add, cast_one, one_div],
  sorry,
  simp only [ne.def, div_eq_zero_iff],
  push_neg,
  split,
  norm_cast,
  exact succ_ne_zero n,
  exact (1:ℝ).exp_ne_zero,
  simp only [ne.def, div_eq_zero_iff, cast_eq_zero], 
  push_neg,
  split,
  exact hn,
  exact (1:ℝ).exp_ne_zero,
  norm_cast,
  linarith,
  norm_cast,
  simp only [nat.mul_eq_zero, bit0_eq_zero, nat.one_ne_zero, false_or],
  exact hn,
  norm_cast,
  exact factorial_ne_zero n,
  norm_cast,
  exact factorial_ne_zero (n + 1),
  exact real.add_group,
  exact covariant_swap_add_lt_of_covariant_add_lt ℝ,
end

lemma test (a b c: ℝ ) :b≠ 0→ c≠ 0→  (a/(b*c)) = a/b/c :=
begin
  sorry,
end


lemma bn_bounded_below: ∀ (n : ℕ), bn n > 3/(4:ℝ) - 1/2*log 2 :=
begin
  sorry,
end

lemma monotone_convergence (bn : ℕ → ℝ) (c : ℝ)
(h_sd: ∀ (n : ℕ),  bn n > bn n.succ)
(h_bounded: ∀ (n:ℕ), bn n > c):
∃ (b : ℝ), tendsto (λ (n : ℕ),  bn n)
 at_top (𝓝  b)  :=
begin
 use (Inf {(bn n : ℝ)| (n:ℕ)}),
 sorry,
end

lemma bn_has_limit_b: ∃ (b : ℝ), tendsto
(λ (n : ℕ),  bn n)
  at_top (𝓝  b) :=
begin
  sorry,
end

lemma an_bounded_by_pos_constant:
∀ (n : ℕ), an n > exp(3/(4:ℝ) - 1/2*log 2) :=
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
