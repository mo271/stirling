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
import analysis.special_functions.integrals
import data.real.pi.wallis

import part2a

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums

open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open filter
open nat


-- part 2b of https://proofwiki.org/wiki/Stirling%27s_Formula

--uses an
lemma sub_seq_tendsto {an : ℕ → ℝ} {A : ℝ} (h: tendsto an at_top (𝓝 A)) :
  tendsto (λ (n : ℕ), an (2 * n)) at_top (𝓝 A) :=
h.comp (tendsto_id.const_mul_at_top' two_pos)

noncomputable def cn (n : ℕ) : ℝ := ((real.sqrt (2 * n) * ((n / (exp 1)) ^ n)) ^ 4) * 2 ^ (4 * n) /
  (((real.sqrt (4 * n) * (((2 * n) / (exp 1))) ^ (2 * n))) ^ 2 * (2 * n + 1))

--uses cn,
lemma rest_cancel (n : ℕ) : (n : ℝ) / (2 * n + 1) = cn n :=
begin
  rw cn,
  have h₀ : 4 = 2 * 2, by refl,
  rw [mul_pow, mul_pow, h₀, pow_mul, sq_sqrt, sq_sqrt],
  cases n,
  rw [cast_zero, zero_div, mul_zero, zero_pow, zero_mul, zero_mul, zero_div],
  exact two_pos,
  have h₁ : 2 * (n.succ : ℝ) + 1 ≠ 0 :=
  begin
    norm_cast,
    exact succ_ne_zero (2*n.succ),
  end,
  have h₂ : exp 1 ≠ 0, from exp_ne_zero 1,
  have h₃ : (n.succ : ℝ) ≠ 0, by exact cast_ne_zero.mpr (succ_ne_zero n),
  field_simp,
  repeat {rw [← pow_mul]},
  rw [← h₀, mul_assoc 2 n.succ 2, mul_left_comm 2 n.succ 2, ← h₀],
  rw [mul_pow (2 : ℝ) _ (n.succ * 4), mul_comm 4 n.succ],
  ring_nf,
  all_goals {norm_cast, linarith},
end

--uses : cn, rest_cancel ,
lemma rest_has_limit_one_half: tendsto (λ (n : ℕ), cn n) at_top (𝓝 (1 / 2)) :=
begin
  apply (tendsto.congr rest_cancel),
  have h : tendsto (λ (x : ℕ), (((x : ℝ) / (2 * (x : ℝ) + 1))⁻¹))
    at_top (𝓝 (((1 : ℝ) / 2))⁻¹) :=
  begin
    have hsucc: tendsto (λ (x : ℕ), (((x.succ : ℝ) / (2 * (x.succ : ℝ) + 1))⁻¹)) at_top
      (𝓝 (((1 : ℝ) / 2))⁻¹) :=
    begin
      have hx: ∀ (x : ℕ), (2 : ℝ) + x.succ⁻¹ = ((x.succ : ℝ) / (2 * x.succ + 1))⁻¹ :=
      begin
        intro x,
        have hxne : (x.succ : ℝ) ≠ 0 := nonzero_of_invertible (x.succ : ℝ),
        field_simp,
      end,
      simp only [one_div, inv_inv],
      apply (tendsto.congr hx),
      have h_right : tendsto (λ (x : ℕ), ((x : ℝ))⁻¹) at_top (𝓝 0) :=
        tendsto_inverse_at_top_nhds_0_nat,
      have h_left : tendsto (λ (x : ℕ), ((2 : ℝ))) at_top (𝓝 2) := tendsto_const_nhds,
      have g := tendsto.add h_left ((tendsto_add_at_top_iff_nat 1).mpr h_right),
      simp only [add_zero] at g,
      exact g,
    end,
    exact (tendsto_add_at_top_iff_nat 1).mp hsucc,
  end,
  have h2: ((1 : ℝ) / 2)⁻¹ ≠ 0 :=
  begin
    simp only [one_div, inv_inv, ne.def, bit0_eq_zero,
    one_ne_zero, not_false_iff],
  end,
  have g:= tendsto.inv₀ h h2,
  simp only [inv_inv, one_div] at g,
  simp only [one_div],
  exact g,
end

--uses : an
lemma an_aux3 (a : ℝ) (hane: a ≠ 0) (ha : tendsto (λ (n : ℕ), an n) at_top (𝓝  a)) :
  tendsto (λ (n : ℕ), (1 / (an n)) ^ 2) at_top (𝓝 ((1 / a) ^ 2)) :=
begin
 have h := tendsto.inv₀ ha hane,
 rw ← one_div at h,
 have hainv : ∀ (n : ℕ), (an n)⁻¹ = 1 / (an n) :=
 begin
   intro n,
   rw ← one_div,
 end,
 have h_congr := tendsto.congr hainv h,
 apply tendsto.pow h_congr 2,
end



--uses: an, cn, wn -- that's it??
--One can still save some calculations by reordering the haves
lemma expand_in_limit (n : ℕ) (hn : n ≠ 0) : (an n) ^ 4 * (1 / (an (2 * n))) ^ 2 * cn n = wn n :=
begin
  rw [an, an, cn, wn],
  have : (4 : ℝ) = (2 : ℝ) * 2, by norm_cast,
  rw this,
  rw [cast_mul 2 n, cast_two, ←mul_assoc],
  rw sqrt_mul (mul_self_nonneg 2) (n : ℝ),
  rw sqrt_mul_self zero_le_two,
  have h₀ : (n : ℝ) ≠ 0, from cast_ne_zero.mpr hn,
  have h₁ : sqrt (2 * (n : ℝ)) ≠ 0,
    from sqrt_ne_zero'.mpr (mul_pos two_pos (cast_pos.mpr (zero_lt_iff.mpr hn))),
  have h₂ : (exp 1) ≠ 0, from exp_ne_zero 1,
  have h₃ : ((2 * n).factorial : ℝ) ≠ 0, from cast_ne_zero.mpr (factorial_ne_zero (2 * n)),
  have h₄ : sqrt (n: ℝ) ≠ 0, from sqrt_ne_zero'.mpr (cast_pos.mpr (zero_lt_iff.mpr hn)),
  have h₅ : (((2 * n) : ℕ) : ℝ) ≠ 0,
    from cast_ne_zero.mpr (mul_ne_zero two_ne_zero hn),
  have h₆ : sqrt (4 * (n : ℝ)) ≠ 0,
    from sqrt_ne_zero'.mpr (mul_pos four_pos (cast_pos.mpr (zero_lt_iff.mpr hn))),
  have h₇ : 2 * (n : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2*n)},
  field_simp,
  ring_nf,
end

--uses: wn, expand_in_limit
lemma expand_in_limit' (n : ℕ) :
  (an n.succ) ^ 4 * (1 / (an (2 * n.succ))) ^ 2 * cn n.succ = wn n.succ :=
 begin
   exact expand_in_limit n.succ (succ_ne_zero n),
 end

--uses: rest_has_limit_one_half, expand_in_limit', wn, an_aux4
lemma second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : tendsto an at_top (𝓝 a)) :
  tendsto wn at_top (𝓝 (a ^ 2 / 2)):=
begin
  rw tendsto_succ wn (a ^ 2 / 2),
  apply tendsto.congr expand_in_limit',
  let qn := λ (x : ℕ), an x ^ 4 * (1 / an (2 * x)) ^ 2 * cn x,
  have hqn : ∀ (x : ℕ), qn x.succ = an x.succ ^ 4 * (1 / an (2 * x.succ)) ^ 2 * cn x.succ := by tauto,
  apply tendsto.congr hqn,
  rw ←tendsto_succ qn (a ^ 2 / 2),
  have has : tendsto (λ (n : ℕ), an n ^ 4 * (1 / an (2 * n)) ^ 2) at_top (𝓝 (a ^ 2)) :=
  begin
    have haright := sub_seq_tendsto (an_aux3 a hane ha),
    have haleft := (tendsto.pow ha 4),
    have g := tendsto.mul  haleft haright,
    have a_pow : a ^ 4 * (1 / a) ^ 2  = a ^ 2 :=
    begin
      field_simp,
      ring,
    end,
    rw a_pow at g,
    exact g,
  end,
  have h := tendsto.mul has rest_has_limit_one_half,
  rw one_div (2 : ℝ) at h,
  rw div_eq_mul_inv _,
  exact h,
end

--uses : second_wallis_limit, wallis_consequence, an
--uses : an_has_pos_limit_a,  pi_and_a, an
lemma an_has_limit_sqrt_pi : tendsto (λ (n : ℕ), an n) at_top (𝓝 (sqrt π)) :=
begin
  have ha := an_has_pos_limit_a,
  cases ha with a ha,
  cases ha with hapos halimit,
  have hπ : π / 2 = a ^ 2 / 2 := tendsto_nhds_unique wallis_consequence
    (second_wallis_limit a (ne_of_gt hapos) halimit),
  field_simp at hπ,
  rw ← (sq_sqrt (le_of_lt pi_pos)) at hπ,
  have h := (sq_eq_sq (sqrt_nonneg π) (le_of_lt hapos)).mp hπ,
  rw ← h at halimit,
  exact halimit,
end
