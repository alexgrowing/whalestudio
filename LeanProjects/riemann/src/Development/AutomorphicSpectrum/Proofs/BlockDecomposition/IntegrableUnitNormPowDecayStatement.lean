import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableUnitNormPowDecay
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_unit_norm_pow_decay : ∀ σ : ℝ, 0 < σ → σ < 1 →
    Integrable (fun a : ℂˣ => ‖(a : ℂ)‖ ^ σ * dd a + ‖(a : ℂ)‖ ^ (σ + 1) * dd a) mulC := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.Radial.integrable_weight | exact GlobalTheory.CompanionTheory.GodementFE.Radial.integrable_weight | (intros; apply GlobalTheory.CompanionTheory.GodementFE.Radial.integrable_weight <;> assumption)
