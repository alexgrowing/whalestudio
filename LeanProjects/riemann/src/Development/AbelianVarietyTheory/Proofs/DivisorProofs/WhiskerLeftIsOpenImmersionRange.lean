import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_isOpenImmersion_range :
    ∀ (S : Scheme.{0}) (A T Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left →
      IsOpenImmersion (A ◁ z).left ∧ ∀ x, x ∈ Set.range (A ◁ z).left ↔ (snd A T).left x ∈ Set.range z.left := by
  intro S A T Z z hz
  have hc : pullback.snd A.hom Z.hom ≫ z.left = (A ◁ z).left ≫ pullback.snd A.hom T.hom := by
    rw [Over.whiskerLeft_left, pullback.lift_snd]
  have hsq : IsPullback (pullback.snd A.hom Z.hom) (A ◁ z).left z.left (pullback.snd A.hom T.hom) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst A.hom T.hom) (v₂₂ := T.hom) (h₃₁ := A.hom) ?_ hc
      (IsPullback.of_hasPullback A.hom T.hom).flip
    have e1 : (A ◁ z).left ≫ pullback.fst A.hom T.hom = pullback.fst A.hom Z.hom := by
      rw [Over.whiskerLeft_left, pullback.lift_fst, Category.comp_id]
    have e2 : z.left ≫ T.hom = Z.hom := Over.w z
    rw [e1, e2]
    exact (IsPullback.of_hasPullback A.hom Z.hom).flip
  have hsnd : (snd A T).left = pullback.snd A.hom T.hom := by simp
  refine ⟨?_, fun x => ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq hz
  · rw [hsnd]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨pullback.snd A.hom Z.hom y, ?_⟩
      rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]
    · rintro ⟨w, hw⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := z.left) (g := pullback.snd A.hom T.hom) w x hw
      refine ⟨hsq.isoPullback.inv p, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hp2]

end GlobalTheory
