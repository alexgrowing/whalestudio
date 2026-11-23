import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableRadialCutoffWeight
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_radial_cutoff_weight : ∀ σ : ℝ, 0 < σ → σ < 1 → Integrable (fun p : ℝ × ℝ =>
    (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
      (GlobalTheory.CompanionTheory.PerUInt.phi p.1 * GlobalTheory.CompanionTheory.PerUInt.phi p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.PerUInt.Outer.integrable_firstColumn | exact GlobalTheory.CompanionTheory.PerUInt.Outer.integrable_firstColumn | (intros; apply GlobalTheory.CompanionTheory.PerUInt.Outer.integrable_firstColumn <;> assumption)
