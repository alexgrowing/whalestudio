import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem app_bijective_of_flat_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R)
    (p : Z ⟶ Y) (q : Z ⟶ S), QuasiCompact π → QuasiSeparated π → Function.Bijective π.appTop.hom → Flat y →
    IsPullback p q y π → ∀ V : Y.Opens, Function.Bijective (p.app V).hom := by
  intro R _ S Y Z π y p q hqc hqs hbij hy H V
  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hV : IsIso (p.app V) := GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens p (fun W ↦
    have : IsAffine W.1 := W.2
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback
      ((isPullback_morphismRestrict p W.1).flip.paste_horiz H.flip)) V
  exact (ConcreteCategory.isIso_iff_bijective _).mp hV

end GlobalTheory.Mum
