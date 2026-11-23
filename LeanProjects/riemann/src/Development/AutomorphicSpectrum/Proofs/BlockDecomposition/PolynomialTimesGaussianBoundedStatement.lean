import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTimesGaussianBounded
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_times_gaussian_bounded : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | exact GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | (intros; apply GlobalTheory.CompanionTheory.EisTube.polyGaussBdd <;> assumption)
