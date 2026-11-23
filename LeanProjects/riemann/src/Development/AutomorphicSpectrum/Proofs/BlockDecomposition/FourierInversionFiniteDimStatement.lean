import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionFiniteDim
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_inversion_finite_dim : ∀ (ι : Type) [Fintype ι] (g : (ι → ℝ) → ℂ), Continuous g → MeasureTheory.Integrable g →
    MeasureTheory.Integrable (fun t : ι → ℝ =>
      ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) →
    ∀ y : ι → ℝ, (∫ t : ι → ℝ, (∫ y', g y' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) = g y := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.fourierInvCoord | exact GlobalTheory.CompanionTheory.EisTube.fourierInvCoord | (intros; apply GlobalTheory.CompanionTheory.EisTube.fourierInvCoord <;> assumption)
