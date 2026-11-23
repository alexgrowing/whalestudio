import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralIoiCompConstDivChangeOfVar
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_Ioi_comp_const_div_change_of_var : ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w → ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t = ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | exact GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | (intros; apply GlobalTheory.lintegral_Ioi_comp_const_div_mul_div <;> assumption)
