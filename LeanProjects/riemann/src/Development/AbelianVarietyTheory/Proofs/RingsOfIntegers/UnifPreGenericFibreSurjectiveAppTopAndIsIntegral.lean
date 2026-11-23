import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isIntegral_left_of_isAbelianScheme_field {K : Type} [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  obtain ⟨-, hs, -, hc⟩ := hA
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton (f := A.hom)
  exact isIntegral_of_smooth_field_of_connectedSpace A.hom

theorem unifPre_genericFibre_surjective_appTop_and_isIntegral :
    GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom ∧ IsIntegral (pullback G.hom (jK R)) := by
  intro hGF R _ _ I D A G _ _ U
  have hAi : IsIntegral A.A.left := isIntegral_left_of_isAbelianScheme_field A.A A.isAb
  have hw : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  have : IsIso U.gen.hom.left := (Over.forget _).map_isIso U.gen.hom
  refine ⟨?_, ?_⟩
  · have hb := hGF _ A.A A.isAb
    rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    have : IsIso U.gen.hom.left.appTop := inferInstanceAs (IsIso (U.gen.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso (U.gen.hom.left.appTop)).surjective.comp hb.surjective
  · show IsIntegral ((Over.pullback (jK R)).obj G).left
    have : Nonempty ((Over.pullback (jK R)).obj G).left :=
      ⟨U.gen.inv.left (Classical.arbitrary A.A.left)⟩
    exact isIntegral_of_isOpenImmersion U.gen.hom.left

end GlobalTheory
