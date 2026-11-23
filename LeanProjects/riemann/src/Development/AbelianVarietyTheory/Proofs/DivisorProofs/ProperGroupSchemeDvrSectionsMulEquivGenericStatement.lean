import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGeneric
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
theorem _root_.GlobalTheory.T.properGroupScheme_dvr_sections_mulEquiv_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  first | exact @GlobalTheory.LevExt.sections_generic_mulEquiv | exact GlobalTheory.LevExt.sections_generic_mulEquiv | (intros; apply GlobalTheory.LevExt.sections_generic_mulEquiv <;> assumption)
