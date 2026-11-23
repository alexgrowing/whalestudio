import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjective
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_in_product_projective : ∀ (K : Type) [Field K] (M r : ℕ) (X' : Scheme.{0}) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)), IsClosedImmersion j → IsProjOver (j ≫ pullback.fst _ _ ≫ PSpace.str K M) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Segre.isProjOver_of_closed_product | exact GlobalTheory.CompanionTheory.Ar.SncBase.Segre.isProjOver_of_closed_product | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Segre.isProjOver_of_closed_product <;> assumption)
