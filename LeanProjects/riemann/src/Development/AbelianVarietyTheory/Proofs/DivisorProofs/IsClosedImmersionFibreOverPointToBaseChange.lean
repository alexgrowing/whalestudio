import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem isClosedImmersion_kerι : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  intro R _ A T V _ φ H h hh
  have hP : IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom T.hom
  have w : pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) ≫ T.hom := by
    rw [Category.assoc]; exact pullback.condition
  let g : pullback A.hom (φ ≫ T.hom) ⟶ (A ⊗ T).left :=
    hP.lift (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) w
  have hg1 : g ≫ (fst A T).left = pullback.fst A.hom (φ ≫ T.hom) := hP.lift_fst _ _ _
  have hg2 : g ≫ (snd A T).left = pullback.snd A.hom (φ ≫ T.hom) ≫ φ := hP.lift_snd _ _ _
  have ht : IsPullback g (pullback.snd A.hom (φ ≫ T.hom)) (snd A T).left φ := by
    refine IsPullback.of_right (h₁₂ := (fst A T).left) (h₂₂ := T.hom) ?_ hg2 hP
    rw [hg1]
    exact IsPullback.of_hasPullback A.hom (φ ≫ T.hom)
  have hs : IsPullback (pullback.fst (h ≫ snd A T).left φ)
      ((kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)) (h.left ≫ (snd A T).left) φ := by
    have e1 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom) = pullback.snd (h ≫ snd A T).left φ :=
      pullback.lift_snd _ _ _
    rw [e1, ← Over.comp_left]
    exact IsPullback.of_hasPullback _ _
  have hsq : pullback.fst (h ≫ snd A T).left φ ≫ h.left = (kerι A φ h).left ≫ g := by
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, hg1]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, hg2, ← Over.comp_left, pullback.condition]
      exact congrArg (· ≫ φ) (pullback.lift_snd _ _ _).symm
  have hpb : IsPullback (pullback.fst (h ≫ snd A T).left φ) (kerι A φ h).left h.left g :=
    IsPullback.of_bot hs hsq ht
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb hh

end GlobalTheory.TwistFlat
