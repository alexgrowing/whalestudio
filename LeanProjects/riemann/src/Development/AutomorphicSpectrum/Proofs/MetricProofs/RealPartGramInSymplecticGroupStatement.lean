import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealPartGramInSymplecticGroup
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
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_part_gram_in_symplectic_group : ∀ (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re) ∈ Matrix.symplecticGroup (Fin g) ℝ →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re).PosDef →
    ∃ (bs' : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (ρ : ℝ),
      0 < ρ ∧ ρ ^ 2 ≤ 2 * g ∧
      (∀ α β, (hermForm Hm (bs' α : Fin g → ℂ) (bs' β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) ∧
      (hermForm Hm (bs' (Sum.inl 0) : Fin g → ℂ) (bs' (Sum.inl 0) : Fin g → ℂ)).re = ρ ^ 2 ∧
      (∀ l : Λ, l ≠ 0 → ρ ^ 2 ≤ (hermForm Hm (l : Fin g → ℂ) (l : Fin g → ℂ)).re) ∧
      (Matrix.of fun i j : Fin g => (hermForm Hm (bs' (Sum.inl i) : Fin g → ℂ) (bs' (Sum.inl j) : Fin g → ℂ)).re).det ≤
        ρ ^ 2 * (2 * g) ^ (g - 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NformRed.symplectic_reduction_basis | exact GlobalTheory.CompanionTheory.Ar.NformRed.symplectic_reduction_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.NformRed.symplectic_reduction_basis <;> assumption)
