import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfCommGroupNsmulSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow <;> assumption)
