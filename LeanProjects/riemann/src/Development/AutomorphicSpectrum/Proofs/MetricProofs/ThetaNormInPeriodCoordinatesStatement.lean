import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaNormInPeriodCoordinates
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_norm_in_period_coordinates : ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (h Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ),
    X.IsSymm → Y.PosDef →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh (periodMatrix X Y) a c (h.mulVec z)) →
    ∀ (u₁ u₂ : Fin g → ℝ) (z : Fin g → ℂ),
      h.mulVec z = (periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) + (fun i => (u₂ i : ℂ)) →
      ‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) = ‖κ‖ * thetaNorm X Y a c u₁ u₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Nform.norm_mul_canTh | exact GlobalTheory.CompanionTheory.Ar.Nform.norm_mul_canTh | (intros; apply GlobalTheory.CompanionTheory.Ar.Nform.norm_mul_canTh <;> assumption)
