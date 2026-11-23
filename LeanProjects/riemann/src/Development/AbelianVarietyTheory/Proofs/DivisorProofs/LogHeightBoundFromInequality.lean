import Mathlib
open scoped ComplexOrder Matrix

namespace GlobalTheory

theorem lieSlope_numerical_end : ∀ (g : ℕ) (C' : ℝ), 0 ≤ C' → ∃ C : ℝ, ∀ h s : ℝ, 0 ≤ h → (∀ n' : ℕ, 2 ≤ n' → Even n' → ((n' : ℝ) + 1) * (-h / 2 - (g / 4) * Real.log (2 * Real.pi)) ≤ -((n' : ℝ) * (n' + 1) / 2) * s + ((n' : ℝ) * (n' + 1) / 4) * Real.log (Real.exp 1 * (4 * n') * n') + ((n' : ℝ) + 1) * (1 / 2 + Real.log (Nat.factorial g) / 2 + (g / 2) * Real.log (4 * n') + g * C' + (g / 2) * Real.log (2 + h))) → s ≤ Real.log (2 + h) + C := by
  intro g C' hC'
  refine ⟨100 + 10 * (g : ℝ) + Real.log (Nat.factorial g) + g * C', ?_⟩
  intro h s hh H
  have key := H (2 * ⌊h⌋₊ + 2) (by omega) ⟨⌊h⌋₊ + 1, by ring⟩
  set N : ℝ := ((2 * ⌊h⌋₊ + 2 : ℕ) : ℝ) with hN
  have hNv : N = 2 * (⌊h⌋₊ : ℝ) + 2 := by rw [hN]; push_cast; ring
  have hfl : (⌊h⌋₊ : ℝ) ≤ h := Nat.floor_le hh
  have hfl2 : h < (⌊h⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one h
  have hf0 : (0 : ℝ) ≤ (⌊h⌋₊ : ℝ) := Nat.cast_nonneg _
  have hN2 : (2 : ℝ) ≤ N := by linarith
  have hNh : h + 1 ≤ N := by linarith
  have hNup : N ≤ 2 * h + 2 := by linarith
  have hNpos : 0 < N := by linarith
  set G : ℝ := (g : ℝ) with hGdef
  have hG : 0 ≤ G := Nat.cast_nonneg _
  have hlg : Real.log (2 + h) ≤ 1 + h := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 + h by linarith)]
  have hl4 : Real.log (4 * N) ≤ 4 * N := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 * N by linarith)]
  have hlp : Real.log (2 * Real.pi) ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 * Real.pi by positivity)
    linarith [Real.pi_le_four]
  have hlf : 0 ≤ Real.log (Nat.factorial g : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.factorial_pos g))
  have hL : Real.log (Real.exp 1 * (4 * N) * N) ≤ 47 + 2 * Real.log (2 + h) := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have hpos : 0 < Real.exp 1 * (4 * N) * N := by positivity
    have hNN : N * N ≤ 4 * (2 + h) ^ 2 := by nlinarith
    have hle : Real.exp 1 * (4 * N) * N ≤ 48 * (2 + h) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right he.le (mul_self_nonneg N), Real.exp_pos 1]
    calc Real.log (Real.exp 1 * (4 * N) * N) ≤ Real.log (48 * (2 + h) ^ 2) := Real.log_le_log hpos hle
      _ = Real.log 48 + 2 * Real.log (2 + h) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 47 + 2 * Real.log (2 + h) := by
        linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 48 by norm_num)]
  have key2 : -h / 2 - (G / 4) * Real.log (2 * Real.pi) ≤ -(N / 2) * s + (N / 4) * Real.log (Real.exp 1 * (4 * N) * N) + (1 / 2 + Real.log (Nat.factorial g) / 2 + (G / 2) * Real.log (4 * N) + G * C' + (G / 2) * Real.log (2 + h)) := by
    have hp : 0 < N + 1 := by linarith
    refine le_of_mul_le_mul_left ?_ hp
    exact key.trans_eq (by ring)
  have f1 := mul_le_mul_of_nonneg_left hlp hG
  have f2 := mul_le_mul_of_nonneg_left hl4 hG
  have f3 := mul_le_mul_of_nonneg_left hN2 (mul_nonneg hG hC')
  have f4 := mul_le_mul_of_nonneg_left (show Real.log (2 + h) ≤ N by linarith) hG
  have f5 := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ N by linarith) hlf
  have f6 := mul_le_mul_of_nonneg_left hL hNpos.le
  have f7 := mul_le_mul_of_nonneg_left hN2 hG
  have f8 : 0 ≤ G * N := mul_nonneg hG hNpos.le
  refine le_of_mul_le_mul_left ?_ hNpos
  linarith

end GlobalTheory
