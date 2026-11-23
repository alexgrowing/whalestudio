import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSqGradientIdentity
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_sq_gradient_identity : ∀ {e : ℕ} (k : Fin e) (z : Fin e → ℂ), z k ≠ 0 → DifferentiableAt ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z ∧ ∀ w : Fin e → ℂ, (fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z w) ^ 2 + (fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z (Complex.I • w)) ^ 2 = 4 * ‖w k‖ ^ 2 / ‖z k‖ ^ 2 := by
  first | exact @GlobalTheory.logNormSq_coord_fderiv_sq_add_sq | exact GlobalTheory.logNormSq_coord_fderiv_sq_add_sq | (intros; apply GlobalTheory.logNormSq_coord_fderiv_sq_add_sq <;> assumption)
