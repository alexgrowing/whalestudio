import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem evO_constO (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R) :
    evO G (constO G r) = r := by
  have hw : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  have h1 := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left ⊤ trivial
  have h2 := congrArg (fun q => q.hom ((G.hom.appLE ⊤ ⊤ (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) h1
  refine h2.trans ?_
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (by simp) ≫
      (η[G]).left.app ⊤ ≫ (Functor.mapIso (Spec (CommRingCat.of R)).presheaf
        (eqToIso (show (η[G]).left ⁻¹ᵁ ⊤ = ⊤ by simp)).op ≪≫ Scheme.ΓSpecIso (CommRingCat.of R)).hom = 𝟙 _ := by
    rw [Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE_assoc]
    simp [hw]
    rw [show Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ (by simp) = 𝟙 _ from
      (Scheme.Hom.appLE_eq_app (𝟙 (Sp R))).trans (Scheme.Hom.id_app ⊤)]
    simp
  exact congrArg (fun q => q.hom r) key

end GlobalTheory.FormalOrigin
