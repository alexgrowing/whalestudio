import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodIntegrandMajorant
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_integrand_majorant : ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 8 ≤ N → ∃ C : ℝ, ∀ h : Ad3.LR.M22, (Matrix.of h).det ≠ 0 →
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) * ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N ≤
      C * (GlobalTheory.CompanionTheory.PerUInt.gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
        (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 0) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 0) * (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 1) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 1)))) := by
  first | exact @GlobalTheory.CompanionTheory.PerUInt.pointwise_gamma_bound | exact GlobalTheory.CompanionTheory.PerUInt.pointwise_gamma_bound | (intros; apply GlobalTheory.CompanionTheory.PerUInt.pointwise_gamma_bound <;> assumption)
