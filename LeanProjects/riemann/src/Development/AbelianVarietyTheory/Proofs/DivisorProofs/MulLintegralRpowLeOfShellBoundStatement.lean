import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulLintegralRpowLeOfShellBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_lintegral_rpow_le_of_shell_bound' : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (h : X → ℝ) (d : ℝ) (B : ℝ≥0∞), Measurable h → (∀ x, 0 < h x) → 0 < d → (∀ j : ℕ, μ {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (d * j))) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ ≤ 2 * B := by
  first | exact @GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound | exact GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound | (intros; apply GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound <;> assumption)
