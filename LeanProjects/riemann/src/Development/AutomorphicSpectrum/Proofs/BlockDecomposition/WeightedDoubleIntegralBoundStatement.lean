import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedDoubleIntegralBound
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_double_integral_bound : ∀ (g φ : ℝ → ℝ), Measurable g → Measurable φ → Integrable g → Integrable φ →
    (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ φ x) → (∀ x, φ x ≤ 1) → ∀ α β : ℝ, α ≠ 0 → β ≠ 0 →
    Integrable (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)) ∧
    ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2) ≤ (∫ x, g x) * (∫ x, φ x) / max |α| |β| := by
  first | exact @GlobalTheory.CompanionTheory.Shear.integral_shear_le | exact GlobalTheory.CompanionTheory.Shear.integral_shear_le | (intros; apply GlobalTheory.CompanionTheory.Shear.integral_shear_le <;> assumption)
