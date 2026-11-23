import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj Limits

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

def regIso (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => h.inj p (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩

def regPt (h : IsCptGen ξ) (p : Cpt ξ) : Sp (regAt ξ p) ⟶ X :=
  spMap (regIso h p).toRingHom ≫ X.fromSpecStalk p.1

theorem genMap_regIso_symm (h : IsCptGen ξ) (p : Cpt ξ) (a : regAt ξ p) :
    genMap ξ p ((regIso h p).symm a) = a := by
  exact congrArg Subtype.val ((regIso h p).apply_symm_apply a)

set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes {p q : Cpt ξ} (hs : q.1 ⤳ p.1) (s : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ p s := by
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

theorem regAt_le {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p ≤ regAt ξ q := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, genMap_specializes hs s⟩

theorem spMap_genMap_fromSpecStalk (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (x := ξ (IsLocalRing.closedPoint Ω)) (y := p.1) p.2,
    ← Category.assoc, ← Spec.map_comp] at h2
  exact h2

theorem spMap_algebraMap_regPt (h : IsCptGen ξ) (p : Cpt ξ) : spMap (algebraMap (regAt ξ p) Ω) ≫ regPt h p = ξ := by
  have e : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun x => rfl
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  exact spMap_genMap_fromSpecStalk p

abbrev regIncl {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p →+* regAt ξ q := Subring.inclusion (regAt_le hs)

theorem spMap_regIncl_regPt (h : IsCptGen ξ) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    spMap (regIncl hs) ≫ regPt h p = regPt h q := by
  have e : (regIncl hs).comp (regIso h p).toRingHom =
      (regIso h q).toRingHom.comp (X.presheaf.stalkSpecializes hs).hom :=
    RingHom.ext fun s => Subtype.ext (genMap_specializes hs s).symm
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

def castPt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y) {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : LieModel G y E := e ▸ M

theorem castPt_pt_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (a : E) :
    ((castPt e M).pt a).left = (M.pt a).left := by
  subst e
  rfl

end GlobalTheory.CompanionTheory.Ar.LieStalk
