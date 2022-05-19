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

example (a b : ℝ) (ha: 0 < a) (hb: 0 < b) (hab: log a ≤ log b): a ≤ b :=
begin
  exact (log_le_log ha hb).mp hab,
end

lemma monotone_convergence (bn : ℕ → ℝ) (c : ℝ) (h_sd: ∀ (a b : ℕ), a ≤ b →  bn b ≤ bn a)
(h_bounded: ∀ (n:ℕ), bn n>= c): ∃ (b : ℝ), tendsto bn at_top (𝓝  b)  :=
begin
 have c_is_lower_bound: (lower_bounds (set.range bn)).nonempty :=
 begin
   use c,
   intros,
   rw lower_bounds,
   simp only [set.mem_range, forall_exists_index, forall_apply_eq_imp_iff', set.mem_set_of_eq],
   exact h_bounded,
 end,
 let x := (Inf (set.range bn)),
 have h: is_glb (set.range bn) x :=
 begin
   refine real.is_glb_Inf (set.range bn) (set.range_nonempty bn) c_is_lower_bound,
 end,
 use x,
 refine tendsto_at_top_is_glb _ _,
 rw antitone,
 exact h_sd,
 exact h,
end

example: real.sqrt 2 ^ 8 = 2 ^ 4 :=
begin
  have h: 8 = 2 * 4 := by linarith,
  rw h,
  rw pow_mul,
  have g: (0 : ℝ) ≤ 2 := zero_le_two,
  rw sq_sqrt g,
end

example:  real.sqrt 2 ^ 4 = 2 ^ 2 :=
begin
  have h: 4 = 2 * 2 := by linarith,
  rw h,
  rw pow_mul,
  have g: (0 : ℝ) ≤ 2 := zero_le_two,
  rw sq_sqrt g,
end

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
