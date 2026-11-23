import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StereographicMeasureChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stereographic_measure_change : ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      ∫⁻ t in Set.Ioo (0:ℝ) 1, g t := by
  first | exact @GlobalTheory.FibLine.lintegral_comp_fsDens | exact GlobalTheory.FibLine.lintegral_comp_fsDens | (intros; apply GlobalTheory.FibLine.lintegral_comp_fsDens <;> assumption)
