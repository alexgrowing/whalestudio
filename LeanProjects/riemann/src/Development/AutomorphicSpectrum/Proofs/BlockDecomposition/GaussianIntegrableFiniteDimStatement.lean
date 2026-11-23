import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianIntegrableFiniteDim
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_integrable_finite_dim : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.gaussInt | exact GlobalTheory.CompanionTheory.EisTube.gaussInt | (intros; apply GlobalTheory.CompanionTheory.EisTube.gaussInt <;> assumption)
