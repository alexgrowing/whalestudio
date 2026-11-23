import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetMatrixSandwichLinearMap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_matrix_sandwich_linear_map : ∀ (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ) (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ)), (∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) → LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first | exact @GlobalTheory.MatMulDet.det_real_mul_mul | exact GlobalTheory.MatMulDet.det_real_mul_mul | (intros; apply GlobalTheory.MatMulDet.det_real_mul_mul <;> assumption)
