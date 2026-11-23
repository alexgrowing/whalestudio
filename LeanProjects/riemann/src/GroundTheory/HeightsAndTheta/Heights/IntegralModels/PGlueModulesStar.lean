import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace GlueModulesStar

section Multi

abbrev starShape (ι : Type*) : MulticospanShape where
  L := Option ι
  R := ι
  fst := fun _ => none
  snd := some

variable {C : Type*} [Category C] {ι : Type*}

lemma isIso_ι_none {I : MulticospanIndex (starShape ι) C} {K : Multifork I} (hK : IsLimit K)
    (h : ∀ j, IsIso (I.snd j)) : IsIso (K.ι none) := by
  let k : ∀ a, I.left none ⟶ I.left a := fun a => match a with
    | none => 𝟙 _
    | some j => haveI := h j; I.fst j ≫ inv (I.snd j)
  have hk : ∀ b, k ((starShape ι).fst b) ≫ I.fst b = k ((starShape ι).snd b) ≫ I.snd b := by
    intro b; simp [k]
  refine ⟨⟨Multifork.IsLimit.lift hK k hk, ?_, ?_⟩⟩
  · apply Multifork.IsLimit.hom_ext hK
    rintro (_ | j)
    · simp [k]
    · have hc := K.condition j
      dsimp at hc
      simp [k, reassoc_of% hc]
  · simp [k]

lemma isIso_ι_some [DecidableEq ι] {I : MulticospanIndex (starShape ι) C} {K : Multifork I}
    (hK : IsLimit K) (i : ι) (hi : IsIso (I.fst i)) (h : ∀ j, j ≠ i → IsIso (I.snd j)) :
    IsIso (K.ι (some i)) := by
  let s₀ : I.left (some i) ⟶ I.left none := I.snd i ≫ @inv _ _ _ _ (I.fst i) hi
  let k : ∀ a, I.left (some i) ⟶ I.left a := fun a => match a with
    | none => s₀
    | some j => if hj : j = i then eqToHom (by rw [hj]) else
        haveI := h j hj; s₀ ≫ I.fst j ≫ inv (I.snd j)
  have hk : ∀ b, k ((starShape ι).fst b) ≫ I.fst b = k ((starShape ι).snd b) ≫ I.snd b := by
    intro b
    by_cases hb : b = i
    · subst hb; simp [k, s₀]
    · simp [k, hb]
  have h0 : K.ι (some i) ≫ s₀ = K.ι none := by
    have hc := K.condition i
    dsimp at hc
    simp [s₀, ← reassoc_of% hc]
  refine ⟨⟨Multifork.IsLimit.lift hK k hk, ?_, ?_⟩⟩
  · apply Multifork.IsLimit.hom_ext hK
    rintro (_ | j)
    · simpa [k] using h0
    · by_cases hj : j = i
      · subst hj; simp [k]
      · have := h j hj
        have hc := K.condition j
        dsimp at hc
        simp only [Category.assoc, Multifork.IsLimit.fac, Category.id_comp, k, dif_neg hj]
        rw [reassoc_of% h0, reassoc_of% hc, IsIso.hom_inv_id, Category.comp_id]
  · simp [k]

end Multi

section Sheaf

universe u

set_option backward.isDefEq.respectTransparency false in
open Scheme.Modules in

lemma isIso_unit_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] (M : Z.Modules)
    (O : Z.Opens) (hO : O ≤ f.opensRange) :
    IsIso (((pullbackPushforwardAdjunction f).unit.app M).app O) := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
    (pullbackPushforwardAdjunction f) M, Hom.comp_app, restrictAdjunction_unit_app_app,
    pushforward_map_app]
  have h1 : f ''ᵁ f ⁻¹ᵁ O = O := by
    rw [f.image_preimage_eq_opensRange_inf]; exact inf_eq_right.mpr hO
  have : IsIso (homOfLE (f.image_preimage_le O)) :=
    ⟨⟨homOfLE h1.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have : IsIso (((restrictAdjunction f).leftAdjointUniq
      (pullbackPushforwardAdjunction f)).hom.app M) := inferInstance
  exact IsIso.comp_isIso' inferInstance inferInstance

open Scheme.Modules in

lemma isIso_homEquiv_symm {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] {E : Z.Modules}
    {M : Y.Modules} (φ : E ⟶ (pushforward f).obj M) (h : ∀ O : Y.Opens, IsIso (φ.app (f ''ᵁ O))) :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv _ _).symm φ) := by
  have key : ((pullbackPushforwardAdjunction f).homEquiv _ _).symm φ =
      (restrictFunctorIsoPullback f).inv.app E ≫ (restrictFunctor f).map φ ≫
        (restrictAdjunction f).counit.app M := by
    rw [Adjunction.homEquiv_counit, ← Adjunction.leftAdjointUniq_hom_app_counit
      (restrictAdjunction f) (pullbackPushforwardAdjunction f) M, restrictFunctorIsoPullback]
    simp only [NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]
  have : IsIso ((restrictFunctor f).map φ) := by
    rw [Hom.isIso_iff_isIso_app]
    intro O
    exact h O
  rw [key]
  infer_instance

open Scheme.Modules in

def transMap {A B Z : Scheme.{u}} (f : A ⟶ B) (h : B ⟶ Z) {k : A ⟶ Z} (e : f ≫ h = k)
    {M : B.Modules} {N : A.Modules} (χ : (Scheme.Modules.pullback f).obj M ⟶ N) :
    (pushforward h).obj M ⟶ (pushforward k).obj N :=
  (pushforward h).map ((pullbackPushforwardAdjunction f).homEquiv _ _ χ) ≫
    (pushforwardComp f h).hom.app N ≫ (pushforwardCongr e).hom.app N

set_option backward.isDefEq.respectTransparency false in
open Scheme.Modules in

lemma isIso_transMap_app {A B Z : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f] (h : B ⟶ Z)
    {k : A ⟶ Z} (e : f ≫ h = k) {M : B.Modules} {N : A.Modules} (χ : (Scheme.Modules.pullback f).obj M ⟶ N)
    [IsIso χ] (O : Z.Opens) (hO : h ⁻¹ᵁ O ≤ f.opensRange) :
    IsIso ((transMap f h e χ).app O) := by
  simp only [transMap, Hom.comp_app, pushforward_map_app, Adjunction.homEquiv_unit,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app]
  have := isIso_unit_app f M (h ⁻¹ᵁ O) hO
  exact IsIso.comp_isIso' (IsIso.comp_isIso' this inferInstance)
    (IsIso.comp_isIso' (IsIso.id _) inferInstance)

open Scheme.Modules in

lemma homEquiv_pullbackCompIso {T Y Z : Scheme.{u}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) {M : T.Modules}
    (χ : (Scheme.Modules.pullback g).obj F ⟶ M) :
    (pullbackPushforwardAdjunction k).homEquiv _ _ ((pullbackCompIso e γ).hom ≫ χ) =
      (pullbackPushforwardAdjunction h).homEquiv _ _ γ.hom ≫ transMap g h e χ := by
  subst e
  have hc1 : (pullbackCongr (rfl : g ≫ h = g ≫ h)).inv.app E = 𝟙 _ := by
    simp [pullbackCongr]
  have hc2 : (pushforwardCongr (rfl : g ≫ h = g ≫ h)).hom.app M = 𝟙 _ := by
    ext O : 1
    exact M.presheaf.map_id _
  have key : ∀ (φ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj E) ⟶ M),
      (pullbackPushforwardAdjunction (g ≫ h)).homEquiv _ _ ((pullbackComp g h).inv.app E ≫ φ) =
        ((pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction g)).homEquiv _ _ φ ≫
          (pushforwardComp g h).hom.app M := by
    intro φ
    have hu := unit_conjugateEquiv
      ((pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction g))
      (pullbackPushforwardAdjunction (g ≫ h)) (pullbackComp g h).inv E
    rw [conjugateEquiv_pullbackComp_inv] at hu
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      ← hu, Category.assoc, Category.assoc]
    congr 1
  simp only [pullbackCompIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc, hc1, Category.id_comp, key, transMap, hc2, Category.comp_id,
    Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Category.assoc]

end Sheaf

section Glue

universe u

variable {X : Scheme.{u}} (V : X.Opens) {ι : Type u} (U : ι → X.Opens)
  (G : (V : Scheme.{u}).Modules) (F : ∀ i, (U i : Scheme.{u}).Modules)
  (ψ : ∀ i, (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i))).obj (F i) ≅
    (Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G)

def index : MulticospanIndex (starShape ι) X.Modules where
  left a := match a with
    | none => (Scheme.Modules.pushforward V.ι).obj G
    | some i => (Scheme.Modules.pushforward (U i).ι).obj (F i)
  right i := (Scheme.Modules.pushforward (U i ⊓ V).ι).obj
    ((Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G)
  fst i := transMap (X.homOfLE (inf_le_right : U i ⊓ V ≤ V)) V.ι (X.homOfLE_ι _) (𝟙 _)
  snd i := transMap (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i)) (U i).ι (X.homOfLE_ι _) (ψ i).hom

set_option backward.isDefEq.respectTransparency false in

lemma isIso_ι_none_app (W : X.Opens) (hW : W ≤ V) :
    IsIso ((Multiequalizer.ι (index V U G F ψ) none).app W) := by
  let Fw : X.Modules ⥤ AddCommGrpCat.{u} := Scheme.Modules.toPresheaf X ⋙ (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have : PreservesLimitsOfShape (WalkingMulticospan (starShape ι))
      ((evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)) :=
    evaluation_preservesLimitsOfShape _
  have : PreservesLimitsOfShape (WalkingMulticospan (starShape ι)) Fw :=
    comp_preservesLimitsOfShape _ _
  have hK := Multifork.isLimitMapOfPreserves (Multiequalizer.multifork (index V U G F ψ)) Fw
    (limit.isLimit (index V U G F ψ).multicospan)
  refine isIso_ι_none hK (fun j => isIso_transMap_app _ _ _ _ W ?_)
  rw [Scheme.opensRange_homOfLE]
  intro x hx
  exact ⟨by simp, hW hx⟩

set_option backward.isDefEq.respectTransparency false in

lemma isIso_ι_some_app (hUU : ∀ i j, i ≠ j → U i ⊓ U j ≤ V) (i : ι) (W : X.Opens)
    (hW : W ≤ U i) : IsIso ((Multiequalizer.ι (index V U G F ψ) (some i)).app W) := by
  classical
  let Fw : X.Modules ⥤ AddCommGrpCat.{u} := Scheme.Modules.toPresheaf X ⋙ (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have : PreservesLimitsOfShape (WalkingMulticospan (starShape ι))
      ((evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)) :=
    evaluation_preservesLimitsOfShape _
  have : PreservesLimitsOfShape (WalkingMulticospan (starShape ι)) Fw :=
    comp_preservesLimitsOfShape _ _
  have hK := Multifork.isLimitMapOfPreserves (Multiequalizer.multifork (index V U G F ψ)) Fw
    (limit.isLimit (index V U G F ψ).multicospan)
  refine isIso_ι_some hK i (isIso_transMap_app _ _ _ _ W ?_)
    (fun j hj => isIso_transMap_app _ _ _ _ W ?_)
  · rw [Scheme.opensRange_homOfLE]
    intro x hx
    exact ⟨hW hx, by simp⟩
  · rw [Scheme.opensRange_homOfLE]
    intro x hx
    exact ⟨by simp, hUU i j (Ne.symm hj) ⟨hW hx, by simp⟩⟩

end Glue

set_option backward.isDefEq.respectTransparency false in

theorem proof : GlueModulesStar.Statement := by
  intro X V ι U _ hUU G F ψ
  let I := index V U G F ψ
  have h0 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none)) :=
    isIso_homEquiv_symm V.ι _ (fun O => isIso_ι_none_app V U G F ψ _ (V.ι_image_le O))
  have hi : ∀ i, IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (U i).ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some i))) := fun i =>
    isIso_homEquiv_symm (U i).ι _
      (fun O => isIso_ι_some_app V U G F ψ hUU i _ ((U i).ι_image_le O))
  refine ⟨multiequalizer I,
    asIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none)),
    fun i => asIso (((Scheme.Modules.pullbackPushforwardAdjunction (U i).ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some i))), fun i => ?_⟩
  ext1
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (U i ⊓ V).ι).homEquiv _ _).injective
  have h1 := homEquiv_pullbackCompIso (X.homOfLE_ι (inf_le_right : U i ⊓ V ≤ V))
    (asIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none))) (𝟙 _)
  have h2 := homEquiv_pullbackCompIso (X.homOfLE_ι (inf_le_left : U i ⊓ V ≤ U i))
    (asIso (((Scheme.Modules.pullbackPushforwardAdjunction (U i).ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some i)))) (ψ i).hom
  rw [Category.comp_id] at h1
  rw [Iso.trans_hom, h1, h2]
  simp only [asIso_hom, Equiv.apply_symm_apply]
  exact Multiequalizer.condition I i

end GlueModulesStar

end

end GroundTheory.Heights₂.Heights.Model
