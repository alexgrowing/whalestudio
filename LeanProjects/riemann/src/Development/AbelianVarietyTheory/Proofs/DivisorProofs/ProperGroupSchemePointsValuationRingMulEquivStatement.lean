import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_group_scheme_points_valuationRing_mulEquiv : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsProper G.hom → ∀ u : Sp U ⟶ S, ∃ e : (Over.mk u ⟶ G) ≃* (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), ∀ P, (e P).left = spMap (algebraMap U Ω) ≫ P.left := by
  first | exact @GlobalTheory.ValPts.points_generic_mulEquiv | exact GlobalTheory.ValPts.points_generic_mulEquiv | (intros; apply GlobalTheory.ValPts.points_generic_mulEquiv <;> assumption)
