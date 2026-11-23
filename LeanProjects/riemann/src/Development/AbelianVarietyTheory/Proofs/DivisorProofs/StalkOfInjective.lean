import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

def stalkOf {W : Type} [CommRing W] (z : Sp W) : W →+* (Sp W).presheaf.stalk z :=
  ((Sp W).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom

theorem stalkOf_injective {W : Type} [CommRing W] [IsDomain W] (z : Sp W) : Function.Injective (stalkOf z) :=
  (germ_injective_of_isIntegral (Sp W) (U := ⊤) z trivial).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1

abbrev unitW {W : Type} [CommRing W] (G : Over (Sp W)) [GrpObj G] : Sp W ⟶ G.left := eSec G

abbrev idW (W : Type) [CommRing W] : Sp W ⟶ (𝟙_ (Over (Sp W))).left := 𝟙 (Sp W)

end GlobalTheory.Mum
