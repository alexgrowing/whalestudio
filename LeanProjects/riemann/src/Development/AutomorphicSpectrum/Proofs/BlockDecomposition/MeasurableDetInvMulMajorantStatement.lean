import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDetInvMulMajorant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_det_inv_mul_majorant : ∀ (N : ℕ) (a b : ℂ), Measurable (fun p : M22 × ℂ => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b) := by
  first | exact @GlobalTheory.CompanionTheory.MajC.measurable_jm_scaled | exact GlobalTheory.CompanionTheory.MajC.measurable_jm_scaled | (intros; apply GlobalTheory.CompanionTheory.MajC.measurable_jm_scaled <;> assumption)
