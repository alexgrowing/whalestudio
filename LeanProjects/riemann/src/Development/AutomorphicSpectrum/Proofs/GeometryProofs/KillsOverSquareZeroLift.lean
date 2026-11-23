import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.WeilBound.CoreStatements.AmpleLineBundles.KillsOverOfSquareZeroIdeal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem killsOver_of_sq_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (I : Ideal B), I ^ 2 = ⊥ → KillsOver u Y (spMap (Ideal.Quotient.mk I) ≫ b) → KillsOver u Y b :=
  @CoverDenseAlt.kills_over_of_square_zero_ideal

end GlobalTheory.CompanionTheory.Ar
