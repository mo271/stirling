import tactic
import analysis.special_functions.log
import data.fintype.basic
import algebra.big_operators.basic
import algebra.big_operators.intervals
import data.finset.sum

open_locale big_operators -- notation ∑ for finite sums
open real
open finset
open nat

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
