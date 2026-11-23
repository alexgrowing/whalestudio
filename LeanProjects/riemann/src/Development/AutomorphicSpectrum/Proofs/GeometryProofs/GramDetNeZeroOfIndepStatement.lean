import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndep
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_ne_zero_of_indep : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (f : Fin n → B.carrier), LinearIndependent (𝓞 L) f → B.gramDet σ f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent <;> assumption)
