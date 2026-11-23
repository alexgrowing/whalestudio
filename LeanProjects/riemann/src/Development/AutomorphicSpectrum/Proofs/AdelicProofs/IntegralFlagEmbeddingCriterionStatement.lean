import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IntegralFlagEmbeddingCriterion
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_flag_embedding_criterion : ∀ (K : Type) [Field K] [NumberField K] (r n' : ℕ) (J : ℕ → Fin r → K) (A : ℕ → (K →+* ℂ) → ℝ), (∀ i σ, 0 < A i σ) → (∀ (i : ℕ) (c : Fin r → 𝓞 K), (∀ k < i, ∑ j, (c j : K) * J k j = 0) → IsIntegral ℤ (∑ j, (c j : K) * J i j)) → (∀ i ≤ n', ∃ (σ : K →+* ℂ) (c : Fin r → ℂ), (∀ k < i, ∑ j, c j * σ (J k j) = 0) ∧ ∑ j, c j * σ (J i j) ≠ 0) → (∀ i ≤ n', ∀ (σ : K →+* ℂ) (c : Fin r → ℂ), (∀ k < i, ∑ j, c j * σ (J k j) = 0) → ‖∑ j, c j * σ (J i j)‖ ≤ A i σ * √(∑ j, ‖c j‖ ^ 2)) → 0 ≤ ∑ i ∈ Finset.range (n' + 1), ∑ σ : K →+* ℂ, Real.log (A i σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagSlope.flag_slope | exact GlobalTheory.CompanionTheory.Ar.FlagSlope.flag_slope | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagSlope.flag_slope <;> assumption)
