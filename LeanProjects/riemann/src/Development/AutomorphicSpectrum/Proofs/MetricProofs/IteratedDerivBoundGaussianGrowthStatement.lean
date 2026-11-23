import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowth
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_deriv_bound_gaussian_growth : ∀ (f : ℂ → ℂ) (M lam : ℝ) (n n' i : ℕ), Differentiable ℂ f → 0 < lam → 1 ≤ n → 1 ≤ n' → i ≤ n' → (∀ τ, ‖f τ‖ ≤ M * Real.exp (n * ‖τ‖ ^ 2 * lam ^ 2 / 2)) → ‖iteratedDeriv i f 0‖ ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | exact GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth <;> assumption)
