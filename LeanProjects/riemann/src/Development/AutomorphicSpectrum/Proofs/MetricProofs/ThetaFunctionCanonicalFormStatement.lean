import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalForm
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
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_canonical_form : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (Λ : Submodule ℤ (Fin g → ℂ))
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) (b : ℝ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, c i = 0 ∨ c i = 1 / 2) →
    (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ, h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z)) →
    (∀ l ∈ Λ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z, θ (z + l) = ε *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z) →
    0 < b →
    (∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
      b ^ 2 = (∫ w in Fd, (‖θ w‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm w w).re)) ^ 2) / (volume Fd).toReal) →
    b ^ 2 = ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.mean_sq_fixes_norm_const | exact GlobalTheory.CompanionTheory.Metric.mean_sq_fixes_norm_const | (intros; apply GlobalTheory.CompanionTheory.Metric.mean_sq_fixes_norm_const <;> assumption)
