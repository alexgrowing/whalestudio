import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficient
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_matrix_coefficient : ∀ (n : ℕ) (g g' : Sch (Fin n)), Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  first | exact @GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | exact GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | (intros; apply GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun <;> assumption)
