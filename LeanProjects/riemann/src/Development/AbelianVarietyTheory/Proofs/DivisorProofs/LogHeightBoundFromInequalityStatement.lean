import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequality
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_height_bound_from_inequality : ∀ (g : ℕ) (C' : ℝ), 0 ≤ C' → ∃ C : ℝ, ∀ h s : ℝ, 0 ≤ h → (∀ n' : ℕ, 2 ≤ n' → Even n' → ((n' : ℝ) + 1) * (-h / 2 - (g / 4) * Real.log (2 * Real.pi)) ≤ -((n' : ℝ) * (n' + 1) / 2) * s + ((n' : ℝ) * (n' + 1) / 4) * Real.log (Real.exp 1 * (4 * n') * n') + ((n' : ℝ) + 1) * (1 / 2 + Real.log (Nat.factorial g) / 2 + (g / 2) * Real.log (4 * n') + g * C' + (g / 2) * Real.log (2 + h))) → s ≤ Real.log (2 + h) + C := by
  first | exact @GlobalTheory.lieSlope_numerical_end | exact GlobalTheory.lieSlope_numerical_end | (intros; apply GlobalTheory.lieSlope_numerical_end <;> assumption)
