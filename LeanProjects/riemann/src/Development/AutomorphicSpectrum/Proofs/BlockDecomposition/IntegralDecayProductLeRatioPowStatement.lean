import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralDecayProductLeRatioPow
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_decay_product_le_ratio_pow : ∀ e : ℝ, 0 < e → e < 2 → ∃ c : ℝ, 0 ≤ c ∧ ∀ A D : ℂ, A ≠ 0 → D ≠ 0 →
    Integrable (fun t : ℂ => (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹)) ∧
    ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * (dd (t * A) * dd (t * D)⁻¹) ≤ c * (‖A‖ / ‖D‖) ^ (-e) := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.TInt.tint | exact GlobalTheory.CompanionTheory.GodementFE.TInt.tint | (intros; apply GlobalTheory.CompanionTheory.GodementFE.TInt.tint <;> assumption)
