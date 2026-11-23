import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothIntegralOverUnitCube
import Mathlib
open MeasureTheory Set
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_integral_over_unit_cube : ∀ (E ι : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] (O : Set E) (F : E × (ι → ℝ) → ℂ), IsOpen O → ContDiffOn ℝ ∞ F (O ×ˢ Set.univ) → ContDiffOn ℝ ∞ (fun v => ∫ x in Icc (0 : ι → ℝ) 1, F (v, x)) O := by
  first | exact @GlobalTheory.contDiffOn_setIntegral_Icc_of_contDiffOn_param | exact GlobalTheory.contDiffOn_setIntegral_Icc_of_contDiffOn_param | (intros; apply GlobalTheory.contDiffOn_setIntegral_Icc_of_contDiffOn_param <;> assumption)
