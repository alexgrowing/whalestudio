import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitHeightBoundLogDiscriminant
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicit_height_bound_log_discriminant : ∀ (f r : ℕ) (L n g h rd P : ℝ), 2 ≤ f → 2 ≤ r → 1 ≤ L → (f : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < n → Real.log n ≤ 2 * f * (r : ℝ) ^ 2 * Real.log g → Real.log g ≤ 30 * L → 0 < h → Real.log h ≤ f * Real.log rd + 2 * f * Real.log (1 + f * Real.log rd) → 0 ≤ P → P ≤ 2 ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * √r → n * (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * (h * 3 ^ (2 * f) * ((3 : ℝ) ^ (2 * f * r ^ 2) * rd ^ ((f : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * P ^ f)) ≤ Real.exp (119 * (f * (r : ℝ) ^ 2 * L)) := by
  first | exact @GlobalTheory.CovTop.VolUp.mass_bound_numbers_le_exp | exact GlobalTheory.CovTop.VolUp.mass_bound_numbers_le_exp | (intros; apply GlobalTheory.CovTop.VolUp.mass_bound_numbers_le_exp <;> assumption)
