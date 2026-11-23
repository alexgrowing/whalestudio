import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IteratedDerivativeFactor
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_derivative_factor : ∀ (r : ℕ) (Ψ : Fin r → ℂ → ℂ) (c : Fin r → ℂ) (h F : ℂ → ℂ), (∀ j, AnalyticAt ℂ (Ψ j) 0) → AnalyticAt ℂ F 0 → F 0 ≠ 0 → (∀ᶠ τ in 𝓝 (0 : ℂ), ∑ j, c j * Ψ j τ = h τ * F τ) → ∀ i : ℕ, ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) ↔ ∀ k < i, iteratedDeriv k h 0 = 0) ∧ ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) → ∑ j, c j * iteratedDeriv i (Ψ j) 0 = F 0 * iteratedDeriv i h 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.JetLeib.jet_first_nonzero | exact GlobalTheory.CompanionTheory.Ar.JetLeib.jet_first_nonzero | (intros; apply GlobalTheory.CompanionTheory.Ar.JetLeib.jet_first_nonzero <;> assumption)
