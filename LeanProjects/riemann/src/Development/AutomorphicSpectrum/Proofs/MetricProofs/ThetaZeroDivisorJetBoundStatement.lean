import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaZeroDivisorJetBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_zero_divisor_jet_bound : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (θ : (Fin g → ℂ) → ℂ)
    (L : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)) (i₀ : Fin g ⊕ Fin g) (c₀ : ℝ),
    Differentiable ℂ θ → (∃ w, θ w ≠ 0) →
    (∀ p, L p ∈ Λ ↔ ∃ k : Fin g ⊕ Fin g → ℤ, p = fun α => (k α : ℝ)) →
    (∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) →
    (∃ k : ℤ, c₀ = k / 2) →
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ),
      (∀ i, (m : ℂ) • r i ∈ Λ ∧ θ (r i) ≠ 0) →
      (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → θ w ≠ 0 → ∃! i, w - r i ∈ Λ) →
      Nonempty Ix ∧ Fintype.card Ix ≤
        3 * {i | (1 / 4 : ℝ) ≤ Metric.infDist (L.symm (r i) i₀ + c₀) (Set.range ((↑) : ℤ → ℝ))}.ncard := by
  first | exact @GlobalTheory.CompanionTheory.TorsOff.torsion_off_zeros | exact GlobalTheory.CompanionTheory.TorsOff.torsion_off_zeros | (intros; apply GlobalTheory.CompanionTheory.TorsOff.torsion_off_zeros <;> assumption)
