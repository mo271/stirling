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

import part0

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat


-- part 1 of https://proofwiki.org/wiki/Stirling%27s_Formula

lemma tendsto_succ (an : ℕ → ℝ) (a:ℝ): tendsto an at_top (𝓝 a) ↔
tendsto (λ n : ℕ, (an n.succ)) at_top (𝓝 a) :=
begin
  split,
  {
    intro h,
    -- rw tendsto at h,
    rw tendsto_at_top' at h,
    rw tendsto_at_top',
    intros,
    have g := h s H,
    cases g with m gm,
    use m,
    intro b,
    intro hb,
    have hbsucc: b.succ >= m := le_succ_of_le hb,
    exact gm b.succ hbsucc,
  },
  { intro h,
    -- rw tendsto at h,
    rw tendsto_at_top' at h,
    rw tendsto_at_top',
    intros,
    have g := h s H,
    cases g with m gm,
    use m.succ,
    intro b,
    intro hb,
    cases b,
    exfalso,
    exact not_succ_le_zero m hb,
    have hbm: b >= m := succ_le_succ_iff.mp hb,
    exact gm b hbm,
  },
end

--can one do this with is_compl_even_odd?
lemma finset_sum_even_odd  {f : ℕ → ℝ} (n : ℕ):
∑ k in range n, f k =
(∑ l in (range n).filter(odd), f l) +
(∑ m in (range n).filter(even), f m) :=
begin

  have h_union: ∀ ( n : ℕ), range n  =
  (range n).filter(odd) ∪ (range n).filter(even) :=
  begin
    intro n,
    induction n with d hd,
    simp only [range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, empty_union],
    repeat {rw [range_succ]},
    repeat {rw [filter_insert]},

    by_cases h: even d,
      rw [if_pos h, if_neg (even_iff_not_odd.mp h)],
      rw union_insert,
      exact congr_arg (insert d) hd,
    rw [if_neg h, if_pos (odd_iff_not_even.mpr h)],
    rw insert_union,
    exact congr_arg (insert d) hd,
  end,
  nth_rewrite 0 h_union,
  have h_disjoint: ∀ (n : ℕ), disjoint  ((range n).filter(odd))
     ((range n).filter(even)) :=
  begin
    intro n,
    induction n with d hd,
    simp only [range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, disjoint_empty_right],
    repeat {rw range_succ},
    repeat {rw filter_insert},
    by_cases h: even d,
      rw [if_pos h, if_neg (even_iff_not_odd.mp h)],
      rw disjoint_insert_right,
      split,
        rw [mem_filter, not_and],
        intro h₂,
        exact absurd h₂ not_mem_range_self,
      assumption,
    rw [if_neg h, if_pos (odd_iff_not_even.mpr h)],
      rw disjoint_insert_left,
      split,
        rw [mem_filter, not_and],
        tauto,
      assumption,
  end,
  rw sum_union (h_disjoint n),
end


lemma finset_reindex_odd {f : ℕ → ℝ} (n : ℕ):
∑ l in (range (2*n)).filter(odd), f l = ∑ l in (range n), f (2*l + 1) :=
begin
  induction n with d hd,
  simp only [mul_zero, range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, sum_empty],
  rw [mul_succ, add_succ, add_succ, add_zero],
  repeat {rw range_succ},
  repeat {rewrite [finset.sum_insert]},
  repeat {rewrite [finset.filter_insert]},
  have h₁ : ¬ odd ( 2* d), by
    simp only [odd_iff_not_even, even.mul_right, even_two, not_true, not_false_iff],
  have h₂: odd (2 * d).succ, by
    {simp only [odd_iff_not_even, h₁, even_succ],
    rw ←odd_iff_not_even,
    assumption},

  rw [if_neg h₁, if_pos h₂],

  repeat {rw finset.sum_insert},
  simp only [add_right_inj],
  exact hd,
  rw [mem_filter],
  suffices :(2 * d).succ ∉ range (2 * d),
  begin
  apply not_and.mpr,
  exact not.elim this,
    end,

  rw mem_range,
  exact not_succ_lt_self,

  rw mem_range,
  exact irrefl d,

end



lemma finset_reindex_even {f : ℕ → ℝ} (n : ℕ):
∑ l in (range (2*n)).filter(even), f l = ∑ l in (range n), f (2*l) :=
begin
  induction n with d hd,
  simp only [mul_zero, range_zero, filter_true_of_mem, not_mem_empty, forall_false_left, forall_const, sum_empty],
  rw [mul_succ, add_succ, add_succ, add_zero],
  repeat {rw range_succ},
  repeat {rewrite [finset.sum_insert]},
  repeat {rewrite [finset.filter_insert]},
  have h₁ : even ( 2 * d), by exact even_two_mul d,
  have h₂ : ¬(even ((2 * d).succ)), by  {simp only [even_succ, h₁], tautology},

  rw [if_neg h₂, if_pos h₁],
  rw finset.sum_insert,
  simp only [add_right_inj],
  exact hd,

  rw [mem_filter],
  suffices : (2 * d) ∉ range (2 * d), by tauto,
  rw mem_range,
  exact irrefl (2*d),

  rw mem_range,
  exact irrefl d,
end

noncomputable def an (n : ℕ) : ℝ  := (n.factorial :ℝ )
/ ((real.sqrt(2*(n))*((n/(exp 1)))^n))

--Not needed: already in mathlib
/-lemma power_series_log_add_one (x:ℝ) (hx: |x| < 1):
tendsto (λ m, ∑ n in range m, (-(1 : ℝ))^(n - 1) * x^n / n)
at_top (𝓝 (log (1 + x))) :=
begin
  sorry,
end-/

noncomputable def term (x : ℝ)(n : ℕ) : ℝ :=
   ((-1)*((-x)^(n + 1) / ((n : ℝ) + 1)) + (x^(n + 1)/((n:ℝ) + 1)))

lemma term_def : ∀ (x: ℝ) , term x =(λ n,  ((-1)*((-x)^(n + 1) / ((n : ℝ) + 1)) + (x^(n + 1)/((n:ℝ) + 1)))) :=
begin
  intros,
  refl,
end

lemma log_sum_plus_minus (x : ℝ) (hx: |x| < 1) : tendsto
(λ (m : ℕ),  (∑ k in range m,
(((2:ℝ)*(1/(2*↑k + 1))*(x^(2*↑k + 1)))))) at_top
(𝓝 (log (1+x) -log(1-x)) ):=
begin
  have min_one_not_zero : (-1 : ℝ) ≠ ( 0 : ℝ), by
      simp only [ne.def, neg_eq_zero, one_ne_zero, not_false_iff],
  have h₁, from has_sum_pow_div_log_of_abs_lt_1 hx,
  have h₂', from has_sum_pow_div_log_of_abs_lt_1 (eq.trans_lt (abs_neg x) hx),
  have h₂, from (has_sum_mul_left_iff min_one_not_zero).mp h₂',
  rw [neg_one_mul, neg_neg, sub_neg_eq_add 1 x] at h₂,
  
  have h₃, from has_sum.add h₂ h₁,
  rw [tactic.ring.add_neg_eq_sub] at h₃,
  rw [←term_def x ] at h₃,
  have h₄:= has_sum.tendsto_sum_nat h₃,
  simp only at h₄,
  rw tendsto_congr finset_sum_even_odd at h₄,

  
  have h_min_one_ne_one: ((-1:ℝ) ≠ (1:ℝ)), by linarith,
  
  have h_odd_n: (∀ n : ℕ, (odd n) → (term x n) = 0),
  begin
    intros n hn,
    simp only [term],

    rw [neg_pow],
    have h_even_n_one : even (n+1), by {rw [ add_one, even_succ, ←odd_iff_not_even], apply hn},
    rw [(neg_one_pow_eq_one_iff_even h_min_one_ne_one).mpr h_even_n_one, one_mul ],
    ring_nf,
  end,

  have h_even_n: (∀ n : ℕ, (even n) → (term x n) = ((2 : ℝ) * x ^ (n+1) / ( (n : ℝ) + 1))),
  begin
    intros n hn,
    simp only [term], 
    rw [neg_pow],
    have h_min_one_ne_one: ((-1:ℝ) ≠ (1:ℝ)), by linarith,
    rw pow_succ (-1:ℝ) n,
    rw (neg_one_pow_eq_one_iff_even h_min_one_ne_one).mpr hn,
    ring_nf,
  end,
  

  
  have h_sum_odd : ∀ (m : ℕ), ∑ (n : ℕ) in filter odd (range m),
   term x n = 0 :=
  begin
  intro m, 
  apply sum_eq_zero,
  intros n hn,
  apply h_odd_n,
  rw [mem_filter] at hn,
  exact hn.2,
  end,

  have h_sum_even  : ∀ (m : ℕ) , ∑ (n : ℕ) in filter even (range m), term x n 
    = ∑ (n : ℕ) in filter even (range m), ((2 : ℝ) * x ^ (n+1) / ( (n : ℝ) + 1)) := 
  begin 
  intro m, 
  apply sum_congr,
    refl,
  intros n hn,
  apply h_even_n,
  rw [mem_filter] at hn,
  exact hn.2,
  end,
  
  have h_sum, from 
  (λ l : ℕ, (congr (congr_arg has_add.add (h_sum_odd l)) (h_sum_even l))), 

  rw tendsto_congr h_sum at h₄,
  simp only [zero_add] at h₄,

  have h₅ := tendsto_even_of_tendsto h₄,
  simp only at h₅,

  have h_final : ∀ (m : ℕ), ∑ (n : ℕ) in filter even (range (2 * m)), 2 * x ^ (n + 1) / ((n : ℝ) + 1)
    = (∑ (n : ℕ) in range m, (2 * (1 / (2 * ↑n + 1)) * x ^ (2 * ↑n + 1))):=
  begin
    intro m,
    rw finset_reindex_even,
    apply sum_congr,
    refl,
    intros,
    push_cast,
    generalize : x^(2 * x_1 + 1) = z,
    ring_nf,
    field_simp,
    refl,
  end,

  rw tendsto_congr h_final at h₅,
  exact h₅,
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

lemma power_series_ln (n : ℕ): has_sum
(λ (k : ℕ),
(2:ℝ) * (((1/(2*↑k + 1))*((1/(2*((↑n + 1))^(2*↑k + 1)))))))
(log (↑n.succ / ↑n)) :=
 begin
  have hn : 0 < n:= by sorry,
  rw aux_log,
  have h₀: 0 <  (2 * n +1) := by exact succ_pos',
  have h₁: |(1:ℝ) / (2 * ↑n + 1)| < 1 :=
  begin
    norm_cast,
    rw abs_of_pos,
    rw div_lt_one,
    norm_cast,
    rw add_comm,
    apply lt_add_of_zero_lt_left,
    simp only [canonically_ordered_comm_semiring.mul_pos, succ_pos', true_and, hn],
    norm_cast,
    exact h₀,
    simp only [cast_add, cast_mul, cast_bit0, cast_one, one_div, inv_pos],
    norm_cast,
    exact h₀,
  end,
  let f_left : ℕ → ℝ := λ k, (1 / (2 * n + 1)) ^ (k + 1) / (k + 1),
  have h_left : has_sum f_left (-log (1 - 1 / (2 * ↑n + 1)))
  := has_sum_pow_div_log_of_abs_lt_1 h₁,
  let f_right : ℕ → ℝ := λ k, ((-1) / (2 * n + 1)) ^ (k + 1) / (k + 1),
  have h₂: | ((-1:ℝ) / (2 * ↑n + 1))| < 1 :=
  begin
    rw abs_div,
    rw abs_neg,
    rw abs_div at h₁,
    exact h₁,
  end,
  have h_right: has_sum f_right (-log (1 - (-1) / (2 * ↑n + 1)))
  := has_sum_pow_div_log_of_abs_lt_1 h₂,
  let f : ℕ → ℝ := λ k, (f_left k) + (f_right k),
  have h: has_sum f
  ((-log (1 - 1 / (2 * ↑n + 1))) + (-log (1 - (-1) / (2 * ↑n + 1)))) :=
  has_sum.add h_left h_right,
  have h_sum : summable f :=
  begin
    use ((-log (1 - 1 / (2 * ↑n + 1))) + (-log (1 - (-1) / (2 * ↑n + 1)))),
    exact h,
  end,
  have h_even: has_sum (λ k, f (2*k)) 0 := by sorry,
  have h_even_sum: summable (λ k, f (2*k)) := by sorry,
  have h_odd_sum: summable (λ k, f (2*k + 1)) := by sorry,
  have g := tsum_even_add_odd h_even_sum h_odd_sum,
  have h' := has_sum.tsum_eq h,
  rw ←g at h',
  have h_even' := has_sum.tsum_eq h_even,
  simp only at h_even',
  rw h_even' at h',
  simp only [zero_add] at h',
  --rw summable.has_sum_iff,
  --
  --:= has_sum_pow_div_log_of_abs_lt_1 h₂,
  sorry, sorry,
 end

noncomputable def bn (n : ℕ) : ℝ := log (an n)

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

lemma bn_formula (n : ℕ):  bn n.succ = (log ↑n.succ.factorial) -
1/(2:ℝ)*(log (2*↑n.succ)) - ↑n.succ*log (↑n.succ/(exp 1)) :=
begin
have h3, from  (lt_iff_le_and_ne.mp (zero_lt_sqrt_two_n n.succ (succ_ne_zero n))),
have h4, from  (lt_iff_le_and_ne.mp (n_div_exp1_pow_gt_zero n.succ )),
rw [bn, an, log_div, log_mul, sqrt_eq_rpow, log_rpow, log_pow],
ring,
rw zero_lt_mul_left,
norm_cast,
exact succ_pos n,
exact zero_lt_two,
exact h3.right.symm,
exact h4.right.symm,
norm_cast,
exact n.succ.factorial_ne_zero,
apply (mul_ne_zero h3.right.symm h4.right.symm),
end


lemma bn_strictly_decreasing: ∀ (n : ℕ), bn n.succ > bn n.succ.succ :=
begin
  sorry,
 /- intros n hn,
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
  push_cast,
  rw div_mul_eq_div_mul_one_div _ 2 (n:ℝ),
  rw mul_comm 2 ((n:ℝ) + 1),
  rw mul_div_cancel ((n:ℝ) + 1),

  rw mul_comm ((n:ℝ) +1) (n.factorial:ℝ),
  rw div_mul_eq_div_mul_one_div (n.factorial:ℝ) (n.factorial:ℝ) _,
  rw div_self,
  rw one_mul,
  rw div_div_div_cancel_right,
  rw ←div_eq_mul_one_div _ (n:ℝ),
  rw mul_comm _ (n:ℝ),
  rw ←add_assoc _ _ _,
  rw add_assoc (log (1 / (↑n + 1))) _ _,
  rw ←add_mul,
  rw log_div,
  rw @log_div ((n:ℝ) +1) (exp 1),
  simp only [log_one, zero_sub, log_exp],
  rw add_right_comm,
  rw add_sub,
  rw neg_add_self,
  rw zero_sub,
  rw add_comm,

  squeeze_simp,
  sorry,
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
  -/
end

lemma bn_antitone: ∀ (a b : ℕ), a ≤ b → bn b.succ ≤ bn a.succ :=
begin
  sorry,
end

lemma bn_sub_bn_succ: ∀ (n : ℕ), bn n.succ - bn n.succ.succ = 1/(4*n.succ*(n.succ.succ)) :=
begin
  sorry,
end
-- in library?
lemma has_sum_consecutive_inverses:
  has_sum (λ (k: ℕ), 1/(k.succ*(k.succ.succ)))  1 :=
begin
  library_search,
end

-- some lemma in library that splits off a finite part of an all-positive converging sum?

lemma partial_sum_consecutive_reciprocals:
 ∀ n, ∑ i in range n, (1:ℝ)/(i.succ*(i.succ.succ)) ≤ 1 :=
 begin
   sorry,

 end

lemma bn_bounded_aux: ∀ (n : ℕ), bn 1 - bn n.succ ≤ 1/4 :=
begin
  let bn': (ℕ → ℝ) :=  λ (k : ℕ), bn k.succ,
  intro n,
  calc
  bn 1 - bn n.succ = bn' 0 - bn' n : rfl
   ... = ∑ i in range n, (bn' i - bn' (i + 1)) : by rw ←(sum_range_sub' bn' n)
   ... = ∑ i in range n, (bn i.succ - bn i.succ.succ) : rfl
   ... = ∑ i in range n, 1/(4*i.succ*(i.succ.succ)) :
   begin
     refine sum_congr (rfl) _,
     intros k hk,
     exact bn_sub_bn_succ k,
   end
   ... = ∑ i in range n, (1/4)*(1/(i.succ*(i.succ.succ))) :
   begin
     have hi: ∀ (i:ℕ), (1 : ℝ)/(4*i.succ*(i.succ.succ)) = (1/4)*(1/(i.succ*(i.succ.succ))) :=
     begin
       intro i,
       norm_cast,
       field_simp,
       simp only [one_div, inv_inj],
       ring,
     end,
    refine sum_congr rfl _,
    intros k hk,
    exact hi k,
   end
   ... = 1/4 * ∑ i in range n, 1/(i.succ*(i.succ.succ)) :
   begin
     rw mul_sum,
   end
   ... ≤ 1/4 * 1 :
   begin
     refine (mul_le_mul_left _).mpr _,
     simp only [one_div, inv_pos, zero_lt_bit0, zero_lt_one],
     exact partial_sum_consecutive_reciprocals n,
   end
   ... = 1/4 : by rw mul_one,
end

lemma bn_bounded_by_constant: ∀  (n : ℕ), bn n.succ ≥ 3/(4:ℝ) - 1/2*log 2 :=
begin
  intro n,
  calc
  bn n.succ ≥ bn 1 - 1/4 :sub_le.mp (bn_bounded_aux n)
   ... = (log((1:ℕ).factorial) - 1/2*log(2 * (1 : ℕ)) - (1:ℕ)*log((1:ℕ)/(exp 1))) - 1/4:
   by rw bn_formula 0
   ... = 0 - 1/2*log(2) - log(1/(exp 1)) - 1/4 : by simp only [factorial_one, cast_one, log_one, one_div, mul_one, log_inv, log_exp, mul_neg]
   ... = -1/2*log(2) - log(1/(exp 1)) - 1/4: by ring
   ... = -1/2*log(2) + 1 - 1/4: by simp only [one_div, log_inv, log_exp, sub_neg_eq_add]
   ... =  -1/2*log(2) + 3/4: by ring
   ... =  3/(4:ℝ) - 1/2*log 2: by ring,
end

lemma bn_has_lower_bound:(lower_bounds (set.range (λ (k:ℕ), bn k.succ))).nonempty :=
begin
   use  3/(4:ℝ) - 1/2*log 2 ,
   intros,
   rw lower_bounds,
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact bn_bounded_by_constant,
end

lemma monotone_convergence (bn : ℕ → ℝ) (h_sd: ∀ (a b : ℕ), a ≤ b → bn b ≤ bn a)
(h_bounded: (lower_bounds (set.range bn)).nonempty): ∃ (b : ℝ), tendsto bn at_top (𝓝  b)  :=
begin
 let x := (Inf (set.range bn)),
 have h: is_glb (set.range bn) x :=
 begin
   refine real.is_glb_Inf (set.range bn) (set.range_nonempty bn) h_bounded,
 end,
 use x,
 refine tendsto_at_top_is_glb _ _,
 rw antitone,
 exact h_sd,
 exact h,
end

lemma bn_has_limit_b: ∃ (b : ℝ),
tendsto (λ (n : ℕ),  bn n.succ)  at_top (𝓝  b) :=
begin
  exact monotone_convergence (λ (k:ℕ), bn k.succ) bn_antitone bn_has_lower_bound,
end

/-an_pos can not be proven if we allow n = 0
corrected version below, but dependent lemmas need to be adjusted-/

lemma  an'_pos: ∀ (n : ℕ), 0 < an n.succ :=
begin
  intro n,
  rw an,
  norm_cast,
  simp only [sqrt_mul', cast_nonneg, div_pow],
  field_simp,
  have h₁: 0 < ((n : ℝ) + 1)*((n).factorial : ℝ) :=
  begin
    norm_cast,
    apply mul_pos,
    exact succ_pos n,
    exact factorial_pos (n),
  end,
  have h₂: 0 < exp(1)^n.succ := (pow_pos ((1:ℝ).exp_pos)) n.succ,
  have h₃: 0 < sqrt (2 :ℝ) * sqrt (↑n + 1) * (↑n + 1) ^ (n + 1) :=
  begin
    apply mul_pos,
    apply mul_pos,
    simp only [real.sqrt_pos, zero_lt_bit0, zero_lt_one],
    simp only [real.sqrt_pos, cast_pos],
    norm_cast,
    exact succ_pos n,
    apply pow_pos,
    norm_cast,
    exact succ_pos n,
  end,
  apply mul_pos,
  apply mul_pos h₁ h₂,
  simp only [inv_pos],
  exact h₃,
end

lemma an'_bounded_by_pos_constant:
∀ (n : ℕ), exp(3/(4:ℝ) - 1/2*log 2) ≤ an n.succ:=
begin
  intro n,
  rw  ←(le_log_iff_exp_le (an'_pos n)),
  exact bn_bounded_by_constant n,
end

lemma an'_antitone: ∀ (a b : ℕ), a ≤ b → an b.succ ≤ an a.succ :=
begin
  intros a b,
  intro hab,
  have hab' := succ_le_succ hab,
  have h := bn_antitone a.succ b.succ hab',
  rw bn at h,
  rw bn at h,
  exact (log_le_log (an'_pos b) (an'_pos a)).mp h,
end


lemma an'_has_lower_bound:
(lower_bounds (set.range (λ (k:ℕ), an k.succ))).nonempty :=
begin
   use  exp(3/(4:ℝ) - 1/2*log 2),
   intros,
   rw lower_bounds,
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact an'_bounded_by_pos_constant,
end

lemma an'_has_limit_a :  ∃ (a : ℝ), tendsto
(λ (n : ℕ),  an n.succ) at_top (𝓝 a) :=
begin
  exact monotone_convergence (λ (k:ℕ), an k.succ) an'_antitone an'_has_lower_bound,
end

lemma an_has_limit_a: ∃ (a : ℝ), tendsto
(λ (n : ℕ),  an n)
  at_top (𝓝  a) :=
begin
  have ha := an'_has_limit_a,
  cases ha with x hx,
  rw ←tendsto_succ an x at hx,
  use x,
  exact hx,
end

lemma an_has_pos_limit_a: ∃ (a : ℝ), 0 < a ∧ tendsto
(λ (n : ℕ),  an n)
  at_top (𝓝  a) :=
begin
  have h:= an_has_limit_a,
  cases h with a ha,
  use a,
  split,
  let an' : ℕ → ℝ := λ n, an n.succ,
  rw tendsto_succ an a at ha,
  have a_is_glb: is_glb (set.range an') a := is_glb_of_tendsto_at_top an'_antitone ha,
  have e_lower_bound:   exp(3/(4:ℝ) - 1/2*log 2) ∈ lower_bounds (set.range an') :=
  begin
    intros x hx,
    simp only [set.mem_range] at hx,
    cases hx with k hk,
    rw ←hk,
    exact an'_bounded_by_pos_constant k,
  end,
  have e_le: exp(3/(4:ℝ) - 1/2*log 2) ≤ a := (le_is_glb_iff a_is_glb).mpr e_lower_bound,
  have e_pos: 0 < exp(3/(4:ℝ) - 1/2*log 2) := (3 / 4 - 1 / 2 * log 2).exp_pos,
  exact gt_of_ge_of_gt e_le e_pos,
  exact ha,
end
