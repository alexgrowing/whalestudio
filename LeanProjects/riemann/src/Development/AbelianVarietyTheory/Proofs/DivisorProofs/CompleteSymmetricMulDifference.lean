import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact

set_option autoImplicit false

open MvPolynomial GlobalTheory.LineForm

namespace GlobalTheory.LineForm

theorem hs_term_rec (k j : ℕ) (hj : j ≤ k) :
    (C ((-1) ^ (j + 1) * ((k + 2 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (k + 2 - 2 * (j + 1)) * X 1 ^ (j + 1) :
        MvPolynomial (Fin 2) ℝ) =
      X 0 * (C ((-1) ^ (j + 1) * ((k + 1 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (k + 1 - 2 * (j + 1)) * X 1 ^ (j + 1)) -
        X 1 * (C ((-1) ^ j * ((k - j).choose j : ℝ)) * X 0 ^ (k - 2 * j) * X 1 ^ j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have e1 : j + m + 2 - (j + 1) = m + 1 := by omega
  have e2 : j + m + 1 - (j + 1) = m := by omega
  have e3 : j + m - j = m := by omega
  have e4 : j + m + 2 - 2 * (j + 1) = m - j := by omega
  have e5 : j + m - 2 * j = m - j := by omega
  have e6 : j + m + 1 - 2 * (j + 1) = m - j - 1 := by omega
  rw [e1, e2, e3, e4, e5, e6, Nat.choose_succ_succ']
  rcases lt_or_ge j m with h | h
  · obtain ⟨n, hn⟩ : ∃ n, m - j = n + 1 := ⟨m - j - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]
    simp only [Nat.cast_add, map_mul, map_add, map_pow, map_neg, map_one]
    ring
  · rw [Nat.choose_eq_zero_of_lt (show m < j + 1 by omega)]
    simp only [Nat.cast_add, map_mul, map_add, map_pow, map_neg, map_one, Nat.cast_zero, map_zero]
    ring

theorem hs_add_two (k : ℕ) : hs (k + 2) = X 0 * hs (k + 1) - X 1 * hs k := by
  unfold hs
  rw [Finset.sum_range_succ' _ (k + 2), Finset.sum_range_succ _ (k + 1), Finset.sum_range_succ' _ (k + 1),
    Finset.sum_congr rfl (fun j hj => hs_term_rec k j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))),
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e : k + 2 - (k + 1 + 1) = 0 := by omega
  rw [e]
  simp only [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, map_zero, zero_mul, add_zero, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, mul_one, map_one, one_mul, Nat.sub_zero]
  ring

theorem aeval_hs_mul_sub :
    ∀ k : ℕ, aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) =
      (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp [hs]
  | one =>
    have : hs 1 = X 0 := by simp [hs, Finset.sum_range_succ]
    rw [this, aeval_X]
    simp only [Matrix.cons_val_zero]
    ring
  | more k h0 h1 =>
    rw [hs_add_two, map_sub, map_mul, map_mul, aeval_X, aeval_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (X 0 + X 1) * h1 - (X 0 * X 1) * h0

end GlobalTheory.LineForm
