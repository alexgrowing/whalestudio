import Mathlib
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory

theorem isPreimmersion_SpecTensorTo :
    ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g),
      IsPreimmersion T.SpecTensorTo := by
  intro X Y S f g T
  set a := X.fromSpecResidueField T.x
  set b := Y.fromSpecResidueField T.y
  set c := S.fromSpecResidueField T.s
  have A := T.isPullback_SpecMap_tensor
  have hx : Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) ≫ c = a ≫ f := by
    simp only [a, c, Scheme.residueFieldCongr_inv, Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hy : Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) ≫ c = b ≫ g := by
    simp only [b, c, Scheme.residueFieldCongr_inv, Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have B : IsPullback (Spec.map T.tensorInl) (Spec.map T.tensorInr) (a ≫ f) (b ≫ g) := by
    rw [← hx, ← hy]
    have w : Spec.map T.tensorInl ≫ Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) ≫ c
        = Spec.map T.tensorInr ≫ Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) ≫ c := by
      rw [← Category.assoc, A.w, Category.assoc]
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (fst := Spec.map T.tensorInl)
      (snd := Spec.map T.tensorInr) w
      (fun s => A.lift s.fst s.snd (by rw [← cancel_mono c]; simpa using s.condition))
      (fun s => A.lift_fst _ _ _) (fun s => A.lift_snd _ _ _)
      (fun s m h1 h2 => A.hom_ext (by rw [h1, A.lift_fst]) (by rw [h2, A.lift_snd])))
  have hm : IsPreimmersion (pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 S)
      (by simp) (by simp)) :=
    haveI : MorphismProperty.IsStableUnderComposition (@IsPreimmersion : MorphismProperty Scheme.{0}) :=
      (inferInstance : MorphismProperty.IsMultiplicative
        (@IsPreimmersion : MorphismProperty Scheme.{0})).toIsStableUnderComposition
    MorphismProperty.pullbackMap (P := (@IsPreimmersion : MorphismProperty Scheme.{0})) (inferInstanceAs (IsPreimmersion a))
      (inferInstanceAs (IsPreimmersion b)) rfl rfl
  have key : B.isoPullback.hom ≫ pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 S) (by simp) (by simp)
      = T.SpecTensorTo := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
        Scheme.Pullback.Triplet.specTensorTo_fst]
    · rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
        Scheme.Pullback.Triplet.specTensorTo_snd]
  rw [← key]
  infer_instance

end GlobalTheory
