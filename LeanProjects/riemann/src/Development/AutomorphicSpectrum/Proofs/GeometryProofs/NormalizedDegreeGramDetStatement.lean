import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedDegreeGramDet
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_gram_det : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (n : ℕ) (e : Fin n → B.carrier), LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → B.normDegree ⊤ = -(1 / 2) * mean L (fun σ => Real.log ‖B.gramDet σ e‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree.normDegree_top_eq_mean_gramDet | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree.normDegree_top_eq_mean_gramDet | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree.normDegree_top_eq_mean_gramDet <;> assumption)
