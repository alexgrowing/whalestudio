import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_of_stable_under_generalization_specialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k)), StableUnderGeneralization U → StableUnderSpecialization U → IsOpen U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | exact GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable <;> assumption)
