import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.CardLeSumOfCover

open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

open PI.SqfLab

theorem geom_half_le (k n : ℕ) : ∑ e ∈ Finset.Icc k n, (1 / 2 : ℝ) ^ (e - k) ≤ 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simpa using sum_geometric_two_le (n + 1 - k)

theorem sq_le_four_pow (e : ℕ) (he : 1 ≤ e) : e ^ 2 ≤ 4 ^ (e - 1) := by
  induction e with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have h1 := ih h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel] at h1
      rw [show m + 1 + 1 - 1 = m + 1 by omega, pow_succ 4 m]
      nlinarith

theorem sq_mul_pow_le (t : ℝ) (ht0 : 0 ≤ t) (e : ℕ) (he : 1 ≤ e) :
    (e : ℝ) ^ 2 * t ^ e ≤ t * (4 * t) ^ (e - 1) := by
  have h1 : (e : ℝ) ^ 2 ≤ 4 ^ (e - 1) := by exact_mod_cast sq_le_four_pow e he
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1 ⊢
  calc ((k + 1 : ℕ) : ℝ) ^ 2 * t ^ (k + 1) ≤ 4 ^ k * t ^ (k + 1) := by gcongr
    _ = t * (4 * t) ^ k := by ring

theorem sum_sq_pow_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) (n : ℕ) :
    ∑ e ∈ Finset.Icc 1 n, (e : ℝ) ^ 2 * t ^ e ≤ 2 * t := by
  calc ∑ e ∈ Finset.Icc 1 n, (e : ℝ) ^ 2 * t ^ e
      ≤ ∑ e ∈ Finset.Icc 1 n, t * (1 / 2 : ℝ) ^ (e - 1) := by
        refine Finset.sum_le_sum fun e he => ?_
        refine (sq_mul_pow_le t ht0 e (Finset.mem_Icc.1 he).1).trans ?_
        gcongr
        linarith
    _ = t * ∑ e ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ (e - 1) := by rw [Finset.mul_sum]
    _ ≤ t * 2 := by gcongr; exact geom_half_le 1 n
    _ = 2 * t := by ring

theorem sum_sq_pow_le_two (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) (n : ℕ) :
    ∑ e ∈ Finset.Icc 2 n, (e : ℝ) ^ 2 * t ^ e ≤ 8 * t ^ 2 := by
  calc ∑ e ∈ Finset.Icc 2 n, (e : ℝ) ^ 2 * t ^ e
      ≤ ∑ e ∈ Finset.Icc 2 n, 4 * t ^ 2 * (1 / 2 : ℝ) ^ (e - 2) := by
        refine Finset.sum_le_sum fun e he => ?_
        have he2 := (Finset.mem_Icc.1 he).1
        refine (sq_mul_pow_le t ht0 e (by omega)).trans ?_
        obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
        rw [show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel, pow_succ]
        have : (4 * t) ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
        nlinarith [pow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) ht0) k]
    _ = 4 * t ^ 2 * ∑ e ∈ Finset.Icc 2 n, (1 / 2 : ℝ) ^ (e - 2) := by rw [Finset.mul_sum]
    _ ≤ 4 * t ^ 2 * 2 := by gcongr; exact geom_half_le 2 n
    _ = 8 * t ^ 2 := by ring

theorem card_LS_le (g r n : ℕ) (hn : n ≠ 0) :
    ((LS g r n).card : ℝ) ≤ Real.log n / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  have h1 : 2 ^ (LS g r n).card ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) (Finset.card_filter_le _ _)).trans
      (two_pow_card_primeFactors_le hn)
  have h2 : ((2 : ℝ)) ^ (LS g r n).card ≤ n := by exact_mod_cast h1
  calc ((LS g r n).card : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (LS g r n).card) := by
        rw [Real.log_pow]
    _ ≤ Real.log n := Real.log_le_log (by positivity) h2

end PI.SqfRootsInj.W
