import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivDetEqTraceAdjugate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_det_eq_trace_adjugate : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (B : E → Matrix (Fin n) (Fin n) ℂ) (w : E), (∀ a b, DifferentiableAt ℝ (fun w' => B w' a b) w) → DifferentiableAt ℝ (fun w' => (B w').det) w ∧ ∀ ξ : E, fderiv ℝ (fun w' => (B w').det) w ξ = ((B w).adjugate * dMat B w ξ).trace := by
  first | exact @GlobalTheory.MatDeriv.jacobi_fderiv_det | exact GlobalTheory.MatDeriv.jacobi_fderiv_det | (intros; apply GlobalTheory.MatDeriv.jacobi_fderiv_det <;> assumption)
