import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomain
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoOverField

theorem eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq]
  erw [ExtUnique.pullback_map_left_fst, ← Category.assoc, ← pullback.condition]
  simp

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

variable {U' U S : Scheme.{0}} (k : U' ⟶ U) (j : U ⟶ S)

noncomputable def toBase (A : Over S) : (Over.mk (k ≫ j) ⊗ A).left ⟶ pullback A.hom j :=
  pullback.lift (snd (Over.mk (k ≫ j)) A).left ((fst (Over.mk (k ≫ j)) A).left ≫ k)
    (by rw [Over.w, Category.assoc]; exact (Over.w (fst (Over.mk (k ≫ j)) A)).symm)

theorem toBase_fst (A : Over S) : toBase k j A ≫ pullback.fst A.hom j = (snd (Over.mk (k ≫ j)) A).left :=
  pullback.lift_fst _ _ _

theorem toBase_snd (A : Over S) : toBase k j A ≫ pullback.snd A.hom j = (fst (Over.mk (k ≫ j)) A).left ≫ k :=
  pullback.lift_snd _ _ _

theorem isPullback_snd (T A : Over S) : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem isPullback_toBase (A : Over S) :
    IsPullback (toBase k j A) (fst (Over.mk (k ≫ j)) A).left (pullback.snd A.hom j) k := by
  refine IsPullback.of_right ?_ (toBase_snd k j A) (IsPullback.of_hasPullback A.hom j)
  rw [toBase_fst]
  exact isPullback_snd (Over.mk (k ≫ j)) A

theorem exists_iso_over [Flat k] [Surjective k] [QuasiCompact k] [Mono j] (A B : Over S) [GrpObj A] [GrpObj B]
    (φ : Over.mk (k ≫ j) ⊗ A ≅ Over.mk (k ≫ j) ⊗ B) (hφ : φ.hom ≫ fst _ _ = fst _ _)
    (h₁ : lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A) ≫ φ.hom ≫ snd _ _ = 1)
    (κ : Over.mk (k ≫ j) ⟶ Over.mk j) (g : Over.mk j ⊗ A ⟶ B) (hg : κ ▷ A ≫ g = φ.hom ≫ snd _ _) :
    ∃ f : (Over.pullback j).obj A ≅ (Over.pullback j).obj B,
      η[(Over.pullback j).obj A] ≫ f.hom = η[(Over.pullback j).obj B] ∧
      toBase k j A ≫ f.hom.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
  have hκ : κ.left = k := (cancel_mono j).1 (Over.w κ)
  let s : pullback A.hom j ⟶ (Over.mk j ⊗ A).left := (pullbackSymmetry A.hom j).hom
  have s₁ : s ≫ (fst (Over.mk j) A).left = pullback.snd A.hom j := pullbackSymmetry_hom_comp_fst _ _
  have s₂ : s ≫ (snd (Over.mk j) A).left = pullback.fst A.hom j := pullbackSymmetry_hom_comp_snd _ _
  have hs : toBase k j A ≫ s = (κ ▷ A).left := by
    refine (isPullback_snd (Over.mk j) A).hom_ext ?_ ?_
    · rw [Category.assoc, s₂, toBase_fst, ← Over.comp_left, whiskerRight_snd]
    · rw [Category.assoc, s₁, toBase_snd, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hκ]
  have hw : (s ≫ g.left) ≫ B.hom = pullback.snd A.hom j ≫ j := by
    rw [Category.assoc, Over.w, ← s₁, Category.assoc]
    exact congrArg (s ≫ ·) (Over.w (fst (Over.mk j) A)).symm
  let f : (Over.pullback j).obj A ⟶ (Over.pullback j).obj B :=
    Over.homMk (pullback.lift (s ≫ g.left) (pullback.snd A.hom j) hw) (pullback.lift_snd _ _ _)
  have f₁ : f.left ≫ pullback.fst B.hom j = s ≫ g.left := pullback.lift_fst _ _ _
  have f₂ : f.left ≫ pullback.snd B.hom j = pullback.snd A.hom j := pullback.lift_snd _ _ _
  have key : toBase k j A ≫ f.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
    rw [f₁, ← Category.assoc, hs, ← Over.comp_left, hg]
  have hφ' : φ.hom.left ≫ (fst (Over.mk (k ≫ j)) B).left = (fst (Over.mk (k ≫ j)) A).left := by
    rw [← Over.comp_left, hφ]
  have sq : toBase k j A ≫ f.left = φ.hom.left ≫ toBase k j B := by
    apply pullback.hom_ext
    · rw [Category.assoc, key, Category.assoc, toBase_fst, Over.comp_left]
    · rw [Category.assoc, f₂, Category.assoc, toBase_snd, toBase_snd, ← Category.assoc, hφ']
  have pb : IsPullback (toBase k j A) φ.hom.left f.left (toBase k j B) := by
    refine IsPullback.of_bot ?_ sq (isPullback_toBase k j B)
    rw [hφ', f₂]
    exact isPullback_toBase k j A
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (toBase k j B) :=
    MorphismProperty.of_isPullback (isPullback_toBase k j B).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hi : IsIso f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0}) pb.flip hQ
      (inferInstanceAs (IsIso ((Over.forget S).map φ.hom)))
  have : IsIso ((Over.forget U).map f) := hi
  have : IsIso f := isIso_of_reflects_iso f (Over.forget U)
  refine ⟨asIso f, ?_, key⟩
  have : Epi k := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have one : ∀ (G : Over S) [GrpObj G], (1 : Over.mk (k ≫ j) ⟶ G).left = (k ≫ j) ≫ eSec G := fun G _ => by
      rw [Hom.one_def, Over.comp_left]
      congr 1
    have e : (lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A)).left ≫ toBase k j A =
        k ≫ eSec ((Over.pullback j).obj A) := by
      apply pullback.hom_ext
      · rw [Category.assoc, toBase_fst, ← Over.comp_left, lift_snd, one, Category.assoc, Category.assoc]
        exact congrArg (k ≫ ·) (eSec_pullback_fst j A).symm
      · rw [Category.assoc, toBase_snd, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc]
        exact (Category.id_comp _).trans ((Category.comp_id k).symm.trans
          (congrArg (k ≫ ·) (Over.w η[(Over.pullback j).obj A]).symm))
    refine (cancel_epi k).1 ?_
    change k ≫ (eSec ((Over.pullback j).obj A) ≫ f.left) ≫ pullback.fst B.hom j =
      k ≫ eSec ((Over.pullback j).obj B) ≫ pullback.fst B.hom j
    rw [eSec_pullback_fst, Category.assoc, ← Category.assoc k, ← e, Category.assoc, key, ← Over.comp_left, h₁,
      one, Category.assoc]
  · exact (Over.w _).trans (Over.w _).symm

theorem exists_iso_over_dvr : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P P' : PolAV (Sp V)) (C : Type) [Field C] [Algebra (FractionRing V) C] (φ : TF (R := V) C ⊗ P.A ≅ TF (R := V) C ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (TF (R := V) C) P.A).left) (P'.L.pull (φ.hom ≫ snd (TF (R := V) C) P'.A).left) → ∀ (κ : TF (R := V) C ⟶ TK V) (g : TK V ⊗ P.A ⟶ P'.A), κ ▷ P.A ≫ g = φ.hom ≫ snd _ _ → ∃ Ψ : P.A ≅ P'.A, IsMonHom Ψ.hom ∧ φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom ∧ LBIso P.L (P'.L.pull Ψ.hom.left) := by
  intro hl _ V _ _ _ P P' C _ _ φ hφ h₁ hL κ g hg
  have : Flat (jFK (R := V) C) := FieldBaseChange.flat_spMap (algebraMap (FractionRing V) C)
  have : Surjective (jFK (R := V) C) := FieldBaseChange.surjective_spMap (algebraMap (FractionRing V) C)
  have : QuasiCompact (jFK (R := V) C) := by
    have : IsAffine (TK V).left := inferInstanceAs (IsAffine (Spec _))
    infer_instance
  have : Mono (jK V) := by
    have : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
    infer_instance
  obtain ⟨f, hf₁, hf⟩ := exists_iso_over (jFK (R := V) C) (jK V) P.A P'.A φ hφ h₁ κ g hg
  have hm : IsMonHom f.hom := hl.rigidity _ _ _ (isAbelianScheme_pullback _ _ P.isAb)
    (isAbelianScheme_pullback _ _ P'.isAb) f.hom hf₁
  have hm' : IsMonHom f.inv := inferInstance
  have hs := isSemiAbelian_of_isAbelianScheme P.A P.isAb
  have hs' := isSemiAbelian_of_isAbelianScheme P'.A P'.isAb
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P.A P'.A hs hs' f.hom hm
  obtain ⟨G, ⟨-, eG⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P'.A P.A hs' hs f.inv hm'
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing V (FractionRing V)
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P'.isAb.smooth
  have := P'.isAb.proper
  have : IsIso F := ExtUnique.isIso_of_pullback (jK V) f F G eF eG
  have e : φ.hom ≫ snd _ _ = snd _ _ ≫ F := by
    apply Over.OverMorphism.ext
    rw [← hf, ← eF, Over.comp_left, ← toBase_fst (jFK (R := V) C) (jK V) P.A, Category.assoc]
    exact congrArg (_ ≫ ·) (ExtUnique.pullback_map_left_fst (jK V) F)
  refine ⟨asIso F, hF, e, ?_⟩
  have hN := pull_isLB P'.isLB F.left
  have hβ : jFK (R := V) C ≫ jK V =
      spMap ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V))) := (Spec.map_comp _ _).symm
  refine IsoDescent.lbIso_of_field V C ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))) P.A P.isAb _
    (snd (TF (R := V) C) P.A).left (fst (TF (R := V) C) P.A).left (hβ ▸ isPullback_snd (TF (R := V) C) P.A)
    P.L (P'.L.pull F.left) P.isLB hN ?_ ?_
  · have eF' : eSec P.A ≫ F.left = eSec P'.A := congrArg (·.left) (IsMonHom.one_hom F)
    rw [← CechPic.cls_eq_iff (pull_isLB P.isLB _) (pull_isLB hN _),
      (CechPic.cls_eq_zero_iff _).2 P.rigid, CechPic.cls_pull hN, CechPic.cls_pull P'.isLB, ← CechPic.pull_comp, eF',
      ← CechPic.cls_pull P'.isLB _ (pull_isLB P'.isLB _), (CechPic.cls_eq_zero_iff _).2 P'.rigid]
  · rw [← CechPic.cls_eq_iff (pull_isLB P.isLB _) (pull_isLB P'.isLB _), CechPic.cls_pull P'.isLB, e] at hL
    rw [← CechPic.cls_eq_iff (pull_isLB P.isLB _) (pull_isLB hN _), hL, CechPic.cls_pull hN,
      CechPic.cls_pull P'.isLB, ← CechPic.pull_comp, Over.comp_left]

end GlobalTheory.IsoOverField
