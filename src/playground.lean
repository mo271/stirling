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
import order.filter.basic
import order.bounded_order
import analysis.special_functions.pow

open_locale filter topological_space classical
open_locale big_operators -- notation ∑ for finite sums
open_locale classical real topological_space nnreal ennreal filter big_operators

open real
open finset
open nat
open filter



lemma has_sum_imp_tendsto (f : ℕ → ℝ) (a : ℝ):  has_sum f a
 → tendsto (λ (m : ℕ), (∑ k in range m, f(k))) at_top (𝓝 a):=
 begin
  intro h,
  rw [has_sum, tendsto, le_def] at h,
  rw [tendsto, le_def],
  intros V hV,
  rw [filter.mem_map', at_top, mem_infi],

  have hV'   := (h V hV),
  rw [filter.mem_map', at_top,  mem_infi] at hV',
  cases hV' with U h_U,
  cases h_U with h_Ufin h_U₂,
  cases h_U₂ with g hg,
  cases hg with hg1 hg',

  rw forall_congr (λ s ,@filter.mem_principal (finset ℕ) (g s) (set.Ici s )) at hg1,


  let f_to_U :=   {A : finset ℕ | ∑ (b : ℕ) in A, f b ∈ V},
  let f_range_to_U := {a : ℕ | range a ∈ f_to_U},

  rw set.subset.antisymm_iff at hg',
  cases hg' with hg2 hg3,


  let U_set := h_Ufin.to_finset,
  let U_union := insert 0 (U_set.bUnion id),
  let M := (U_union.sup id).succ,
  have all_U_in_range_M : ∀ (I : U), (I : finset ℕ) ⊆ (range M) :=
  begin
    intro I,
    have : (I : finset ℕ) ∈ U_set, by simp only [set.finite.mem_to_finset, subtype.coe_prop],
    have : (I : finset ℕ) ⊆ U_set.bUnion id, by
      exact subset_bUnion_of_mem id this,
    have  h_I_subs_U_union: (I : finset ℕ) ⊆ U_union, by
      exact finset.subset.trans this (subset_insert 0 (U_set.bUnion id)),
    have : (U_union) ⊆ range M, by exact subset_range_sup_succ (U_union),
    exact subset.trans h_I_subs_U_union this,
  end,

  let U' := insert M (∅: set ℕ),
  existsi U',
  split,
  simp only [set.finite.insert, set.finite_empty],
  let g' := (λ x : U',  (range (x:ℕ) : set ℕ)ᶜ ∪ f_range_to_U ),

  existsi g',
  split,
  intro x,
  have hxM : (x : ℕ) = M, by
  { have := subtype.mem x, simp only [U'] at this,
    simpa only [insert_emptyc_eq] using this},

  rewrite [mem_principal],
  simp only [g'],
  rw ←set.Ici_def,
  apply set.subset_union_of_subset_left,
  rw set.subset_compl_iff_disjoint,
  have : has_inter (set ℕ), by exact set.has_inter,
  rw set.eq_empty_iff_forall_not_mem,
  simp only [set.mem_inter_eq, set.mem_set_of_eq, mem_coe, mem_range, not_and, not_lt, imp_self, forall_const],
  simp only [U'],
  simp only [set.Inter_coe_set, set.mem_insert_iff, set.mem_empty_eq, or_false, subtype.coe_mk, set.Inter_Inter_eq_left],
  rw set.subset_def at hg3,


  have h₁:{x : ℕ | (range x).sum f ∈ V} ⊆ f_range_to_U,
  begin
    rw set.subset_def,
    intro n,
    intro hn,
    rw set.mem_set_of_eq at hn,
    simp only [set.mem_set_of_eq],
    exact hn,
  end,

  have h₂ : (range M: set ℕ)ᶜ ⊆ {x : ℕ | (range x).sum f ∈ V},
  begin
    rw set.subset_def,
    intros n hn,
    simp only [set.mem_compl_eq, mem_coe, mem_range, not_lt, max'_le_iff, mem_insert, mem_bUnion, set.finite.mem_to_finset, id.def,
      exists_prop, forall_eq_or_imp, zero_le', forall_exists_index, and_imp, true_and] at hn,
    rw set.mem_set_of_eq,
    let hgx := hg3 (range n),
    rw set.mem_Inter at hgx,
    have : (∀ I: U, range n ∈ g I) :=
    begin
      intro I,
      have hg1_I, by exact hg1 I,
      have , from all_U_in_range_M I,
      have I_subset_range_n, from this.trans (range_subset.mpr hn),
      simp only at hg1_I,
      have : (range n) ∈ set.Ici (I : finset ℕ), by
        {rw [set.mem_Ici, le_eq_subset], assumption},
      exact set.mem_of_mem_of_subset this hg1_I,
    end,
    have h_range_n := hgx this,
    simp only [set.mem_set_of_eq] at h_range_n,
    assumption,
  end,

  have h₃ : f_range_to_U ⊆ {x : ℕ | (range x).sum f ∈ V},
  begin
    simp only [f_range_to_U, set.mem_set_of_eq],
  end,

  apply set.eq_of_subset_of_subset,
    apply set.subset_union_of_subset_right,
    exact h₁,
  apply set.union_subset,
    exact h₂,
  exact h₃,
  end


 example: (2:ℝ) - 1 = 1 :=
 begin
   linarith,
 end

example (n : ℕ) : 2 ≤ n.succ.succ :=
begin
  rw succ_eq_add_one,
  rw succ_eq_add_one,
  rw add_assoc,
  simp only [le_add_iff_nonneg_left, zero_le'],
end

example (n : ℕ) : ((n + 1).factorial) = (n + 1)*(n.factorial) :=
begin
  rw nat.factorial,
end

lemma log_sum (n : ℕ) :
(real.log n.factorial)  =
(∑ k in (Ico 2 (n.succ) ), real.log k) :=
begin
  cases n,
  simp only [nat.factorial_zero, nat.cast_one, log_one,
  Ico_eq_empty_of_le, nat.one_le_bit0_iff,
  nat.lt_one_iff, sum_empty],
  induction n with d hd,
  simp only [nat.factorial_one, nat.cast_one,
  log_one, Ico_self, sum_empty],
  rw nat.factorial,
  simp only [nat.cast_mul],
  rw log_mul,
  {
  rw hd,
  have ha:  2 ≤ d.succ.succ :=
  begin
    rw succ_eq_add_one,
    rw succ_eq_add_one,
    rw add_assoc,
    simp only [le_add_iff_nonneg_left, zero_le'],
  end,
  rw sum_Ico_succ_top ha,
  simp only [nat.cast_succ],
  ring,
  },
  norm_cast,
  exact succ_ne_zero d.succ,
  norm_cast,
  exact factorial_ne_zero d.succ,
end
