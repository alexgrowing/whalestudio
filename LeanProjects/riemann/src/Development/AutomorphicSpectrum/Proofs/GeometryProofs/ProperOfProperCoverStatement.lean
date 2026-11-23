import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_of_proper_cover : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), IsSeparated p → LocallyOfFiniteType p → (∀ i, IsProper (π i ≫ p)) → (∀ x : X, ∃ i, x ∈ Set.range (π i)) → IsProper p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover | exact GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover <;> assumption)
