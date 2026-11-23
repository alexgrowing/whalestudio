import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapFromSpecStalkOriginCompStructureEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section
namespace GlobalTheory.CoordsOrigin

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

def derHom (D : G.left.presheaf.stalk (origin G) → R) (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = evO G x * D y + evO G y * D x) (hc : ∀ r, D (constO G r) = 0) :
    G.left.presheaf.stalk (origin G) →+* DualNumber R where
  toFun f := TrivSqZeroExt.inl (evO G f) + TrivSqZeroExt.inr (D f)
  map_one' := by
    have h1 : D 1 = 0 := by simpa using hc 1
    ext <;> simp [h1]
  map_mul' x y := by
    ext <;> simp [hmul]
    ring
  map_zero' := by
    have h0 : D 0 = 0 := by simpa using hadd 0 0
    ext <;> simp [h0]
  map_add' x y := by
    ext <;> simp [hadd]

end GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin
theorem exists_tan_of_derivation (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R) (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = evO G x * D y + evO G y * D x) (hc : ∀ r, D (constO G r) = 0) :
    ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  set ψ := derHom G D hadd hmul hc with hψdef
  have hψ : ∀ f, ψ f = TrivSqZeroExt.inl (evO G f) + TrivSqZeroExt.inr (D f) := fun f => rfl
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo' (R := R) (η[G]).left
  haveI hloc : IsLocalHom ψ := ⟨fun a ha => by
    have h2 : IsUnit (ψ a).fst := (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha
    simp only [hψ, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero] at h2
    exact isUnit_of_map_unit (evO G) a h2⟩
  haveI hloc' : IsLocalHom (CommRingCat.ofHom ψ).hom := hloc
  let p : Sp (DualNumber R) ⟶ G.left := spMap ψ ≫ G.left.fromSpecStalk (origin G)
  have hcomp : ψ.comp (constO G) = algebraMap R (DualNumber R) := by
    ext r <;> simp [hψ, evO_constO, hc, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : p ≫ G.hom = (overAt (𝟙 (Sp R)) (DualNumber R)).hom := by
    simp only [p, Category.assoc]
    rw [spMap_fromSpecStalk_origin_hom, hcomp]
    simp [overAt]
  let w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G := Over.homMk p hover
  have hw : smT (𝟙 (Sp R)) 0 w = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, one_left]
    have e1 : (epsMul (0 : R)).comp ψ = (algebraMap R (DualNumber R)).comp (evO G) := by
      ext f <;> simp [hψ, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    have e2 : spMap (evO G) ≫ G.left.fromSpecStalk (origin G) = (η[G]).left :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) (η[G]).left
    change spMap (epsMul (0 : R)) ≫ spMap ψ ≫ G.left.fromSpecStalk (origin G) = _
    have e3 : spMap (epsMul (0 : R)) ≫ spMap ψ = spMap ((epsMul (0 : R)).comp ψ) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have e4 : spMap ((algebraMap R (DualNumber R)).comp (evO G)) = spMap (algebraMap R (DualNumber R)) ≫ spMap (evO G) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [← Category.assoc, e3, e1, e4, Category.assoc, e2]
    simp [overAt]
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw, fun f => ?_⟩
  rw [tanDer_eq]
  have key : (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G (ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw)).symm)).hom ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw)).left =
      CommRingCat.ofHom ψ := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    rw [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom ψ) U _
  rw [key]
  simp [hψ]
end GlobalTheory.CoordsOrigin
