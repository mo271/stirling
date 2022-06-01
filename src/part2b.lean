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
  simp only [cast_zero, mul_zero, zero_div, real.sqrt_zero, zero_mul, zero_pow', ne.def,
    bit0_eq_zero, nat.one_ne_zero, not_false_iff],
  have h1 : 2 * (n.succ : ℝ) + 1 ≠ 0 :=
  begin
    norm_cast,
    exact succ_ne_zero (2*n.succ),
  end,
  have h2 : (4 * (n.succ : ℝ) * ((2 * ↑n.succ / exp 1) ^ 
    (2 * n.succ)) ^ 2) * (2 * ↑n.succ + 1) ≠ 0 :=
  begin
    refine mul_ne_zero _ h1,
    refine mul_ne_zero _ _,
    exact mul_ne_zero four_ne_zero (cast_ne_zero.mpr (succ_ne_zero n)),
    apply pow_ne_zero 2 (pow_ne_zero (2 * n.succ) _),
    any_goals {exact is_domain.to_no_zero_divisors ℝ},
    have : exp 1 ≠ 0, from exp_ne_zero 1,
    have : n.succ ≠ 0, from succ_ne_zero n,
    field_simp, norm_cast, field_simp,
  end,
  repeat {rw [← pow_mul]},
  rw [← h₀, mul_assoc 2 n.succ 2, mul_left_comm 2 n.succ 2, ← h₀],
  have h3: exp 1 ^ (n.succ *4) ≠ 0, by exact pow_ne_zero (n.succ * 4) (exp_ne_zero 1),
  have h4 :  4 ≠ 0, by exact four_ne_zero,
  have h5 : (n.succ : ℝ) ≠ 0, by exact cast_ne_zero.mpr (succ_ne_zero n),
  field_simp,
  rw [mul_pow (2 : ℝ) _ (n.succ * 4), mul_comm 4 n.succ],
  ring_nf,
  all_goals {norm_cast, linarith},
end

--uses : cn, rest_cancel ,
lemma rest_has_limit_one_half: tendsto
(λ (n:ℕ), cn n) at_top (𝓝 (1/2)) :=
begin
 apply (tendsto.congr rest_cancel),
 have h: tendsto (λ (x : ℕ), (((x:ℝ )/ (2 * ↑x + 1))⁻¹))
 at_top (𝓝 (((1:ℝ ) / 2))⁻¹):=
 begin
  have hsucc: tendsto (λ (x : ℕ), (((x.succ:ℝ )/ (2 * ↑x.succ + 1))⁻¹))
  at_top (𝓝 (((1:ℝ ) / 2))⁻¹):=
  begin
    -- this indirection (considering the succ) is taken,
    -- becuase otherwise we would have a hard time
    -- proving hxne
    have hx: ∀ (x:ℕ), (2:ℝ) + x.succ⁻¹ = ((x.succ : ℝ) / (2 * x.succ + 1))⁻¹  :=
    begin
      intro x,
      have hxne: (x.succ : ℝ) ≠ 0 :=
      begin
        exact nonzero_of_invertible ↑(succ x),
      end,
      field_simp,
    end,
    simp only [one_div, inv_inv],
    apply (tendsto.congr (hx)),
    have h_right: tendsto (λ (x : ℕ), ((x : ℝ))⁻¹) at_top (𝓝 0)
      :=tendsto_inverse_at_top_nhds_0_nat,
    have h_left: tendsto (λ (x : ℕ), ((2 : ℝ))) at_top (𝓝 2):=
  tendsto_const_nhds,
    have g:= tendsto.add h_left ((tendsto_add_at_top_iff_nat 1).mpr h_right),
    simp only [add_zero] at g,
    exact g,
  end,
  exact (tendsto_add_at_top_iff_nat 1).mp hsucc,
 end,
 have h2: ((1:ℝ )/2)⁻¹ ≠ 0 :=
 begin
   simp only [one_div, inv_inv, ne.def, bit0_eq_zero,
   one_ne_zero, not_false_iff],
 end,
 have g:= tendsto.inv₀ h h2,
 simp only [inv_inv, one_div] at g,
 simp only [one_div],
 exact g,
end

--uses an,
lemma an_aux1 (a : ℝ) (ha : tendsto (λ (n : ℕ),  an n) at_top (𝓝  a)) :
  tendsto (λ (n : ℕ), (an n) ^ 4) at_top (𝓝 (a ^ 4)) :=
begin
 exact tendsto.pow ha 4,
end

--uses an
lemma an_aux2 (a : ℝ) (hane: a ≠ 0) (ha : tendsto (λ (n : ℕ),  an n) at_top (𝓝  a)) :
  tendsto (λ (n : ℕ),  (an n)⁻¹) at_top (𝓝 ((a)⁻¹)) :=
begin
  exact tendsto.inv₀ ha hane,
end

--uses : an_aux2, an
lemma an_aux3 (a : ℝ) (hane: a ≠ 0) (ha : tendsto (λ (n : ℕ),  an n) at_top (𝓝  a)) :
  tendsto (λ (n : ℕ), (1 / (an n)) ^ 2) at_top (𝓝 ((1 / a) ^ 2)) :=
begin
 have h := an_aux2 a hane ha,
 rw ← one_div at h,
 have hainv : ∀ (n : ℕ), (an n)⁻¹ = 1 / (an n) :=
 begin
   intro n,
   rw ← one_div,
 end,
 have h_congr := tendsto.congr hainv h,
 apply tendsto.pow h_congr 2,
end

--uses an_aux3, an, sub_seq_tendsto
lemma an_aux4 (a : ℝ) (hane : a ≠ 0) (ha : tendsto (λ (n : ℕ),  an n) at_top (𝓝  a)) :
  tendsto (λ (n : ℕ), (1 / (an (2 * n))) ^ 2) at_top (𝓝 ((1 / a) ^ 2)) :=
begin
  have h := an_aux3 a hane ha,
  exact sub_seq_tendsto h,
end

--uses: an, cn, wn -- that's it??
-- added the assumption hn. Without that the statement is false (I think).
-- With the new assumption, the lemma below does not work anymore...
--One can still save some calculations by reordering the haves
lemma expand_in_limit (n : ℕ) (hn : n ≠ 0) : (an n) ^ 4 * (1 / (an (2 * n))) ^ 2 * cn n = wn n :=
begin
  rw [an, an, cn, wn],
  norm_cast,
  have h1 : ∀ (m : ℕ), ((m ≠ 0) → (sqrt (2 * (m : ℝ)) * ((m : ℝ) / exp 1) ^ m ) ≠ 0) :=
  begin
    intros m hm,
    refine mul_ne_zero _ _,
    refine sqrt_ne_zero'.mpr _, 
    norm_cast, 
    exact nat.mul_pos two_pos (zero_lt_iff.mpr hm),
    apply pow_ne_zero,
    apply div_ne_zero _ (exp_ne_zero 1),
    exact cast_ne_zero.mpr hm,
  end,
  have hn2 : 0 < 2 * n := nat.mul_pos two_pos (zero_lt_iff.mpr hn),
  have h2 : ((((2 * n).factorial) : ℝ) / (sqrt (2 * (((2 : ℕ) * n) : ℝ))* 
    ((((2 : ℕ) * n) : ℝ) / exp 1) ^ (2 * n)) ≠ 0) :=
  begin
    refine div_ne_zero _ _,
    norm_cast,
    exact factorial_ne_zero (2 * n),
    rw [← cast_mul 2 n],
    exact h1 (2 * n) (ne_of_gt hn2), -- this is just h3...
  end,

  have h3: real.sqrt (2 * (((2 : ℕ) * n) : ℝ)) * ((((2 : ℕ) * n) : ℝ) / exp 1) ^ (2 * n) ≠ 0 :=
  begin
    rw [← cast_mul 2 n],
    exact h1 (2 * n) (ne_of_gt hn2),
  end,

  have h4 : (((2 * n).factorial) : ℝ) ^ 2 *  (2 * n + 1) ≠ 0 :=
  begin
    norm_cast,
    refine mul_ne_zero _ _,
      apply pow_ne_zero,
      exact factorial_ne_zero (2 * n),
    exact succ_ne_zero (2 * n),
  end,

  --this is now longer, but doesn't use an involved simp
  have h5 : (real.sqrt 2 * sqrt ↑n * ↑n ^ n) ^ 4 * ((((2 * n).factorial)) * exp 1 ^ (2 * n)) ^ 2 *
   ((exp 1 ^ n) ^ 4 * ((sqrt 4 * sqrt ↑n * (2 * ↑n) ^ (2 * n)) ^ 2 * (2 * n + 1))) ≠ 0 :=
   begin
    norm_cast,
    refine mul_ne_zero _ _,
    refine mul_ne_zero _ _,
    apply pow_ne_zero,
    rw mul_assoc,
    apply mul_ne_zero (sqrt_ne_zero'.mpr two_pos),
    refine mul_ne_zero _ _,
    exact (sqrt_ne_zero'.mpr (cast_pos.mpr (zero_lt_iff.mpr hn))),
    norm_cast,
    apply pow_ne_zero,
    exact hn,
    apply pow_ne_zero,
    refine mul_ne_zero _ _,
    exact (cast_ne_zero.mpr (factorial_ne_zero (2 * n))),
    exact pow_ne_zero (2 * n) (exp_ne_zero 1),
    refine mul_ne_zero _ _,
    rw ← pow_mul,
    exact pow_ne_zero (n * 4) (exp_ne_zero 1),
    refine mul_ne_zero _ _,
    apply pow_ne_zero 2,
    refine mul_ne_zero _ _,
    apply mul_ne_zero (sqrt_ne_zero'.mpr four_pos),
    exact (sqrt_ne_zero'.mpr (cast_pos.mpr (zero_lt_iff.mpr hn))), 
    rw [cast_ne_zero, pow_ne_zero_iff hn2, ← zero_lt_iff],
    exact hn2,
    exact cancel_monoid_with_zero.to_no_zero_divisors,
    exact is_domain.to_no_zero_divisors ℝ,
    exact cast_ne_zero.mpr (succ_ne_zero (2 * n)),
    /-Not needed anymore, right?-/
    --previously:
  --   simp only [cast_pow, cast_mul, cast_bit0, cast_one, cast_add, mul_eq_zero, pow_eq_zero_iff, succ_pos', real.sqrt_eq_zero,
  -- zero_le_bit0, zero_le_one, bit0_eq_zero, one_ne_zero, cast_nonneg, cast_eq_zero, false_or],
  --   push_neg,
  --   split,
  --   split,
  --   split,
  --   exact hn,
  --   norm_cast,
  --   exact ne_of_gt (pow_pos (zero_lt_iff.mpr hn) n),
  --   split,
  --   exact factorial_ne_zero (2*n),
  --   exact ne_of_gt (pow_pos (1:ℝ).exp_pos (2*n)),
  --   split,
  --   exact ne_of_gt (pow_pos (1:ℝ).exp_pos (n)),
  --   split,
  --   split,
  --   exact hn,
  --   norm_cast,
  --   exact ne_of_gt (pow_pos hn2 (2*n)),
  --   norm_cast,
  --   exact succ_ne_zero (2*n),
  end,
  field_simp,
  ring_nf,
  have h6 : real.sqrt 4 ^ 2 = 4 := by simp only [sq_sqrt, zero_le_bit0, zero_le_one],
  have h7 : real.sqrt 2 ^ 8 = 2 ^ 4 :=
  begin
    have h : 8 = 2 * 4 := by linarith,
    rw h,
    rw pow_mul,
    have g : (0 : ℝ) ≤ 2 := zero_le_two,
    rw sq_sqrt g,
  end,
  have h8 : real.sqrt 2 ^ 4 = 2 ^ 2 :=
  begin
    have h : 4 = 2 * 2 := by linarith,
    rw h,
    rw pow_mul,
    have g : (0 : ℝ) ≤ 2 := zero_le_two,
    rw sq_sqrt g,
  end,
  rw [h6, h7, h8],
  ring,
end

--usues: wn, expand_in_limit
lemma expand_in_limit' (n : ℕ) :
  (an n.succ) ^ 4 * (1 / (an (2 * n.succ))) ^ 2 * cn n.succ = wn n.succ :=
 begin
   have hn: n.succ ≠ 0 := succ_ne_zero n,
   exact expand_in_limit n.succ hn,
 end

--uses: rest_has_limit_one_half, expand_in_limit', wn, an_aux1, an_aux4
lemma second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : tendsto an at_top (𝓝 a)) :
  tendsto wn at_top (𝓝 (a^2/2)):=
begin
  rw tendsto_succ wn (a ^ 2 / 2),
  apply tendsto.congr expand_in_limit',
  let qn := λ (x : ℕ), an x ^ 4 * (1 / an (2 * x)) ^ 2 * cn x,
  have hqn : ∀  (x : ℕ), qn x.succ = an x.succ ^ 4 * (1 / an (2 * x.succ)) ^ 2 * cn x.succ := by tauto,
  apply tendsto.congr hqn,
  rw ←tendsto_succ qn (a ^ 2 / 2),
  have hcn := rest_has_limit_one_half,
  have has : tendsto (λ (n : ℕ), an n ^ 4 * (1 / an (2 * n)) ^ 2) at_top (𝓝 (a ^ 2)) :=
  begin
    have haright := an_aux4 a hane ha,
    have haleft := an_aux1 a ha,
    have g := tendsto.mul  haleft haright,
    have a_pow : a ^ 4 * (1 / a) ^ 2  = a ^ 2 :=
    begin
      field_simp,
      ring,
    end,
    rw a_pow at g,
    exact g,
  end,
  have h := tendsto.mul has hcn,
  rw one_div (2 : ℝ) at h,
  rw div_eq_mul_inv _,
  exact h,
end

--uses : second_wallis_limit, wallis_consequence, an
lemma pi_and_a (a : ℝ) (hane : a ≠ 0) (ha : tendsto (λ (n : ℕ),  an n) at_top (𝓝  a)) :
  π / 2 = a ^ 2 / 2 :=
begin
  have h := second_wallis_limit a hane ha,
  have g := wallis_consequence,
  exact tendsto_nhds_unique g h,
end


--uses : an_has_pos_limit_a,  pi_and_a, an
lemma an_has_limit_sqrt_pi : tendsto (λ (n : ℕ), an n) at_top (𝓝 (sqrt π)) :=
begin
  have ha := an_has_pos_limit_a,
  cases ha with a ha,
  cases ha with hapos halimit,
  have hπ : π / 2 = a ^ 2 / 2 := pi_and_a a _ halimit,
  field_simp at hπ,
  have zero_le_pi: 0 ≤ π :=
  begin
    exact le_of_lt pi_pos,
  end,
  rw ← (sq_sqrt zero_le_pi) at hπ,
  have h := (sq_eq_sq (sqrt_nonneg π) (le_of_lt hapos)).mp hπ,
  rw ← h at halimit,
  exact halimit,
  exact ne_of_gt hapos,
end
