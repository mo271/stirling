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
