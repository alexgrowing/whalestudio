import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
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

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

def tvStalk (v : TanM (𝟙 (Sp R)) G) : G.left.presheaf.stalk (origin G) ⟶ CommRingCat.of (DualNumber R) :=
  (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left

instance isLocalHom_tvStalk (v : TanM (𝟙 (Sp R)) G) : IsLocalHom (tvStalk G v).hom := by
  rw [tvStalk, CommRingCat.hom_comp]
  haveI := isLocalHom_of_isIso (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom
  haveI := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left
  exact RingHom.isLocalHom_comp _ _

theorem specMap_fromSpecStalk_congr {X : Scheme.{0}} {A : CommRingCat.{0}} {x y : X} (h : x = y)
    (s : X.presheaf.stalk y ⟶ A) :
    Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ s) ≫ X.fromSpecStalk x =
      Spec.map s ≫ X.fromSpecStalk y := by
  subst h
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem tv_left_eq (v : TanM (𝟙 (Sp R)) G) :
    (tv v).left = Spec.map (tvStalk G v) ≫ G.left.fromSpecStalk (origin G) := by
  rw [tvStalk, specMap_fromSpecStalk_congr (tv_closedPoint G v).symm]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).symm

theorem isLocalHom_epsMul_zero : IsLocalHom (epsMul (0 : R)) :=
  ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩

theorem tvStalk_fst (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)) :
    ((tvStalk G u).hom f).fst = ((tvStalk G v).hom f).fst := by
  haveI := isLocalHom_epsMul_zero (R := R)
  have hl : ∀ w : TanM (𝟙 (Sp R)) G, IsLocalHom (tvStalk G w ≫ CommRingCat.ofHom (epsMul (0 : R))).hom := by
    intro w
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    infer_instance
  have hw : ∀ w : TanM (𝟙 (Sp R)) G, Spec.map (tvStalk G w ≫ CommRingCat.ofHom (epsMul (0 : R))) ≫
      G.left.fromSpecStalk (origin G) = (smT (𝟙 (Sp R)) 0 (tv w)).left := by
    intro w
    rw [smT_left, tv_left_eq G w, Spec.map_comp, Category.assoc]
  have e : Spec.map (tvStalk G u ≫ CommRingCat.ofHom (epsMul (0 : R))) ≫ G.left.fromSpecStalk (origin G) =
      Spec.map (tvStalk G v ≫ CommRingCat.ofHom (epsMul (0 : R))) ≫ G.left.fromSpecStalk (origin G) := by
    rw [hw, hw, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem]
  have e2 := (SpecToEquivOfLocalRing G.left (CommRingCat.of (DualNumber R))).symm.injective
    (a₁ := ⟨origin G, tvStalk G u ≫ CommRingCat.ofHom (epsMul (0 : R)), hl u⟩)
    (a₂ := ⟨origin G, tvStalk G v ≫ CommRingCat.ofHom (epsMul (0 : R)), hl v⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at e3
  have e4 : epsMul (0 : R) ((tvStalk G u).hom f) = epsMul (0 : R) ((tvStalk G v).hom f) := by
    have := congrArg (fun q : G.left.presheaf.stalk (origin G) ⟶ CommRingCat.of (DualNumber R) => q.hom f) e3
    simpa using this
  have e5 := congrArg TrivSqZeroExt.fst e4
  simpa [epsMul] using e5

theorem tanM_eq_of_tanDer : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (u v : TanM (𝟙 (Sp R)) G), (∀ f, tanDer G u f = tanDer G v f) → u = v := by
  intro R _ _ G _ _ u v h
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext
  apply Over.OverMorphism.ext
  have hs : tvStalk G u = tvStalk G v := by
    ext f
    · exact tvStalk_fst G u v f
    · have hu := tanDer_eq G u f
      have hv := tanDer_eq G v f
      exact hu.symm.trans ((h f).trans hv)
  rw [tv_left_eq G u, tv_left_eq G v, hs]

end GlobalTheory.CoordsOrigin
