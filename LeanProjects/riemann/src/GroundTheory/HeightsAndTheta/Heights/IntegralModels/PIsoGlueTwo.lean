import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsIsoGlueTwo
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueModulesStar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace IsoGlueTwo

lemma isIso_app_sup {T : TopCat.{0}} {F G : TopCat.Presheaf AddCommGrpCat.{0} T} (hF : F.IsSheaf)
    (hG : G.IsSheaf) (η : F ⟶ G) (U V : Opens T) (hU : IsIso (η.app (op U)))
    (hV : IsIso (η.app (op V))) (hUV : IsIso (η.app (op (U ⊓ V)))) :
    IsIso (η.app (op (U ⊔ V))) := by
  have lF := TopCat.Sheaf.isLimitPullbackCone ⟨F, hF⟩ U V
  have lG := TopCat.Sheaf.isLimitPullbackCone ⟨G, hG⟩ U V
  have n : ∀ {W W' : Opens T} (i : W ⟶ W') [IsIso (η.app (op W'))] [IsIso (η.app (op W))],
      inv (η.app (op W')) ≫ F.map i.op = G.map i.op ≫ inv (η.app (op W)) := by
    intro W W' i _ _
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← η.naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hw : (G.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op ≫ inv (η.app (op U))) ≫
      F.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op =
      (G.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op ≫ inv (η.app (op V))) ≫
      F.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op := by
    rw [Category.assoc, Category.assoc, n, n, ← G.map_comp_assoc, ← G.map_comp_assoc]
    rfl
  have l₁ := PullbackCone.IsLimit.lift_fst lF _ _ hw
  have l₂ := PullbackCone.IsLimit.lift_snd lF _ _ hw
  change PullbackCone.IsLimit.lift lF _ _ hw ≫ F.map (homOfLE le_sup_left : U ⟶ U ⊔ V).op = _ at l₁
  change PullbackCone.IsLimit.lift lF _ _ hw ≫ F.map (homOfLE le_sup_right : V ⟶ U ⊔ V).op = _ at l₂
  have key : ∀ {W : Opens T} (r : W ⟶ U ⊔ V) (_ : IsIso (η.app (op W)))
      (L : G.obj (op (U ⊔ V)) ⟶ F.obj (op (U ⊔ V)))
      (_ : L ≫ F.map r.op = G.map r.op ≫ inv (η.app (op W))),
      (η.app _ ≫ L) ≫ F.map r.op = 𝟙 _ ≫ F.map r.op ∧
        (L ≫ η.app _) ≫ G.map r.op = 𝟙 _ ≫ G.map r.op := by
    intro W r _ L hL
    constructor
    · rw [Category.assoc, hL, ← Category.assoc, ← η.naturality, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, ← η.naturality, ← Category.assoc, hL, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, Category.id_comp]
  refine ⟨⟨PullbackCone.IsLimit.lift lF _ _ hw, ?_, ?_⟩⟩
  · apply PullbackCone.IsLimit.hom_ext lF
    · exact (key _ hU _ l₁).1
    · exact (key _ hV _ l₂).1
  · apply PullbackCone.IsLimit.hom_ext lG
    · exact (key _ hU _ l₁).2
    · exact (key _ hV _ l₂).2

open Scheme.Modules GlueModulesStar

section Glue

variable {X Z₁ Z₂ T : Scheme.{0}}

def restrictOverlap (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k) (M : X.Modules) :
    (pushforward f).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (pushforward k).obj ((Scheme.Modules.pullback k).obj M) :=
  transMap g f e (pullbackCompIso e (Iso.refl _)).inv

lemma unit_restrictOverlap (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k) (M : X.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫ restrictOverlap g f e M =
      (pullbackPushforwardAdjunction k).unit.app M := by
  have h := homEquiv_pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback f).obj M))
    (pullbackCompIso e (Iso.refl _)).inv
  rw [Iso.hom_inv_id, Iso.refl_hom, Adjunction.homEquiv_id, Adjunction.homEquiv_id] at h
  exact h.symm

lemma transMap_pullback_map (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {M M' : Z₁.Modules} {N : T.Modules} (a : M ⟶ M') (χ : (Scheme.Modules.pullback g).obj M' ⟶ N) :
    transMap g f e ((Scheme.Modules.pullback g).map a ≫ χ) = (pushforward f).map a ≫ transMap g f e χ := by
  simp only [transMap, Adjunction.homEquiv_naturality_left, Functor.map_comp, Category.assoc]

lemma homEquiv_pullbackIsoAlong (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    (pullbackPushforwardAdjunction k).homEquiv _ _ (pullbackIsoAlong e φ).hom =
      (pullbackPushforwardAdjunction f).homEquiv _ _ φ.hom ≫ restrictOverlap g f e B := by
  have h := homEquiv_pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback f).obj A))
    ((Scheme.Modules.pullback g).map φ.hom ≫ (pullbackCompIso e (Iso.refl _)).inv)
  have h2 : (pullbackPushforwardAdjunction f).homEquiv _ _ (𝟙 _) ≫ (pushforward f).map φ.hom =
      (pullbackPushforwardAdjunction f).homEquiv _ _ φ.hom := by
    rw [← Adjunction.homEquiv_naturality_right, Category.id_comp]
  rw [transMap_pullback_map, Iso.refl_hom] at h
  rw [restrictOverlap, ← h2, Category.assoc, ← h]
  simp only [pullbackIsoAlong, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]

lemma pullbackIsoAlong_symm (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    pullbackIsoAlong e φ.symm = (pullbackIsoAlong e φ).symm := by
  ext1
  simp only [pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]

variable (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
  (g₁ : T ⟶ Z₁) (g₂ : T ⟶ Z₂) [IsOpenImmersion g₁] [IsOpenImmersion g₂] {k : T ⟶ X}
  (e₁ : g₁ ≫ f₁ = k) (e₂ : g₂ ≫ f₂ = k)

omit [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion g₁] [IsOpenImmersion g₂] in

lemma unit_condition (M : X.Modules) :
    (pullbackPushforwardAdjunction f₁).unit.app M ≫ restrictOverlap g₁ f₁ e₁ M =
      (pullbackPushforwardAdjunction f₂).unit.app M ≫ restrictOverlap g₂ f₂ e₂ M := by
  rw [unit_restrictOverlap, unit_restrictOverlap]

def isLimit (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) (M : X.Modules) :
    IsLimit (PullbackCone.mk _ _ (unit_condition f₁ f₂ g₁ g₂ e₁ e₂ M)) := by
  set τ₁ := restrictOverlap g₁ f₁ e₁ M
  set τ₂ := restrictOverlap g₂ f₂ e₂ M
  have w := unit_condition f₁ f₂ g₁ g₂ e₁ e₂ M
  suffices hc : IsIso (pullback.lift _ _ w) by
    haveI : IsIso ((limit.isLimit (cospan τ₁ τ₂)).lift (PullbackCone.mk _ _ w)) := hc
    exact IsLimit.ofPointIso (limit.isLimit _)
  have loc : ∀ (W : X.Opens) (a : Bool),
      (W ≤ (if a then f₁.opensRange else f₂.opensRange)) →
      IsIso ((pullback.lift _ _ w).app W) := by
    intro W a hW
    let Fw : X.Modules ⥤ AddCommGrpCat.{0} :=
      toPresheaf X ⋙ (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{0}).obj (op W)
    have : PreservesLimitsOfShape WalkingCospan
        ((evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{0}).obj (op W)) :=
      evaluation_preservesLimitsOfShape _
    have : PreservesLimitsOfShape WalkingCospan Fw := comp_preservesLimitsOfShape _ _
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte] at hW
      have : IsIso (Fw.map τ₁) := isIso_transMap_app g₁ f₁ e₁ _ W (h₂₁ W hW)
      have : IsIso (Fw.map (pullback.snd τ₁ τ₂)) := by
        rw [← PreservesPullback.iso_hom_snd Fw]; infer_instance
      have : IsIso (Fw.map ((pullbackPushforwardAdjunction f₂).unit.app M)) :=
        isIso_unit_app f₂ M W hW
      have hc : Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.snd τ₁ τ₂) =
          Fw.map ((pullbackPushforwardAdjunction f₂).unit.app M) := by
        rw [← Fw.map_comp, pullback.lift_snd]
      have : IsIso (Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.snd τ₁ τ₂)) := by
        rw [hc]; infer_instance
      exact IsIso.of_isIso_comp_right (Fw.map (pullback.lift _ _ w)) (Fw.map (pullback.snd τ₁ τ₂))
    · simp only [↓reduceIte] at hW
      have : IsIso (Fw.map τ₂) := isIso_transMap_app g₂ f₂ e₂ _ W (h₁₂ W hW)
      have : IsIso (Fw.map (pullback.fst τ₁ τ₂)) := by
        rw [← PreservesPullback.iso_hom_fst Fw]; infer_instance
      have : IsIso (Fw.map ((pullbackPushforwardAdjunction f₁).unit.app M)) :=
        isIso_unit_app f₁ M W hW
      have hc : Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.fst τ₁ τ₂) =
          Fw.map ((pullbackPushforwardAdjunction f₁).unit.app M) := by
        rw [← Fw.map_comp, pullback.lift_fst]
      have : IsIso (Fw.map (pullback.lift _ _ w) ≫ Fw.map (pullback.fst τ₁ τ₂)) := by
        rw [hc]; infer_instance
      exact IsIso.of_isIso_comp_right (Fw.map (pullback.lift _ _ w)) (Fw.map (pullback.fst τ₁ τ₂))
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  have hW : W ⊓ f₁.opensRange ⊔ W ⊓ f₂.opensRange = W := by
    rw [← inf_sup_left]; exact inf_eq_left.mpr (le_top.trans hcov)
  rw [← hW]
  exact isIso_app_sup M.isSheaf (pullback τ₁ τ₂).isSheaf (pullback.lift _ _ w).mapPresheaf _ _
    (loc _ true inf_le_right) (loc _ false inf_le_right)
    (loc _ true (inf_le_left.trans inf_le_right))

lemma comp_unit {Z : Scheme.{0}} (f : Z ⟶ X) {A B : X.Modules} (α : A ⟶ B) :
    α ≫ (pullbackPushforwardAdjunction f).unit.app B =
      (pullbackPushforwardAdjunction f).homEquiv _ _ ((Scheme.Modules.pullback f).map α) := by
  rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]

include e₁ e₂ in

lemma hom_ext (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules} (α β : A ⟶ B)
    (h₁ : (Scheme.Modules.pullback f₁).map α = (Scheme.Modules.pullback f₁).map β)
    (h₂ : (Scheme.Modules.pullback f₂).map α = (Scheme.Modules.pullback f₂).map β) : α = β := by
  apply PullbackCone.IsLimit.hom_ext (isLimit f₁ f₂ g₁ g₂ e₁ e₂ hcov h₁₂ h₂₁ B)
  · exact (comp_unit f₁ α).trans ((congrArg _ h₁).trans (comp_unit f₁ β).symm)
  · exact (comp_unit f₂ α).trans ((congrArg _ h₂).trans (comp_unit f₂ β).symm)

lemma exists_hom (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules}
    (φ₁ : (Scheme.Modules.pullback f₁).obj A ⟶ (Scheme.Modules.pullback f₁).obj B)
    (φ₂ : (Scheme.Modules.pullback f₂).obj A ⟶ (Scheme.Modules.pullback f₂).obj B)
    (h : (pullbackPushforwardAdjunction f₁).homEquiv _ _ φ₁ ≫ restrictOverlap g₁ f₁ e₁ B =
      (pullbackPushforwardAdjunction f₂).homEquiv _ _ φ₂ ≫ restrictOverlap g₂ f₂ e₂ B) :
    ∃ α : A ⟶ B, (Scheme.Modules.pullback f₁).map α = φ₁ ∧
      (Scheme.Modules.pullback f₂).map α = φ₂ := by
  have l := isLimit f₁ f₂ g₁ g₂ e₁ e₂ hcov h₁₂ h₂₁ B
  refine ⟨PullbackCone.IsLimit.lift l _ _ h, ?_, ?_⟩
  · apply ((pullbackPushforwardAdjunction f₁).homEquiv _ _).injective
    exact (comp_unit f₁ _).symm.trans (PullbackCone.IsLimit.lift_fst l _ _ h)
  · apply ((pullbackPushforwardAdjunction f₂).homEquiv _ _).injective
    exact (comp_unit f₂ _).symm.trans (PullbackCone.IsLimit.lift_snd l _ _ h)

end Glue

end IsoGlueTwo

theorem IsoGlueTwo.proof : IsoGlueTwo.Statement := by
  intro Y P₁ P₂ P P₁₂ h₁ h₂ hP k₁ k₂ hk A B φ₁ φ₂ hφ
  have e₁ : Y.homOfLE k₁ ≫ Y.homOfLE h₁ = Y.homOfLE (k₁.trans h₁) := Y.homOfLE_homOfLE k₁ h₁
  have e₂ : Y.homOfLE k₂ ≫ Y.homOfLE h₂ = Y.homOfLE (k₁.trans h₁) := Y.homOfLE_homOfLE k₂ h₂
  have hφ' : pullbackIsoAlong e₁ φ₁ = pullbackIsoAlong e₂ φ₂ := hφ
  have hcov : ⊤ ≤ (Y.homOfLE h₁).opensRange ⊔ (Y.homOfLE h₂).opensRange := by
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_sup,
      ← P.ι_preimage_self]
    exact Scheme.Hom.preimage_mono _ hP
  have h₁₂ : ∀ O : (P : Scheme.{0}).Opens, O ≤ (Y.homOfLE h₁).opensRange →
      (Y.homOfLE h₂) ⁻¹ᵁ O ≤ (Y.homOfLE k₂).opensRange := by
    intro O hO
    rw [Scheme.opensRange_homOfLE] at hO ⊢
    refine (Scheme.Hom.preimage_mono _ hO).trans ?_
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
    intro x hx
    have hx2 : P₂.ι x ∈ P₂ := x.2
    exact hk ⟨hx, hx2⟩
  have h₂₁ : ∀ O : (P : Scheme.{0}).Opens, O ≤ (Y.homOfLE h₂).opensRange →
      (Y.homOfLE h₁) ⁻¹ᵁ O ≤ (Y.homOfLE k₁).opensRange := by
    intro O hO
    rw [Scheme.opensRange_homOfLE] at hO ⊢
    refine (Scheme.Hom.preimage_mono _ hO).trans ?_
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
    intro x hx
    have hx1 : P₁.ι x ∈ P₁ := x.2
    exact hk ⟨hx1, hx⟩
  have hhom := congrArg (fun ψ => (Scheme.Modules.pullbackPushforwardAdjunction
    (Y.homOfLE (k₁.trans h₁))).homEquiv _ _ ψ.hom) hφ'
  have hinv := congrArg (fun ψ => (Scheme.Modules.pullbackPushforwardAdjunction
    (Y.homOfLE (k₁.trans h₁))).homEquiv _ _ ψ.symm.hom) hφ'
  simp only [← IsoGlueTwo.pullbackIsoAlong_symm] at hinv
  simp only [IsoGlueTwo.homEquiv_pullbackIsoAlong] at hhom hinv
  obtain ⟨α, hα₁, hα₂⟩ := IsoGlueTwo.exists_hom _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ φ₁.hom φ₂.hom hhom
  obtain ⟨β, hβ₁, hβ₂⟩ := IsoGlueTwo.exists_hom _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ φ₁.inv φ₂.inv hinv
  refine ⟨⟨α, β, ?_, ?_⟩, ?_, ?_⟩
  · apply IsoGlueTwo.hom_ext _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ <;> simp [hα₁, hα₂, hβ₁, hβ₂]
  · apply IsoGlueTwo.hom_ext _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ <;> simp [hα₁, hα₂, hβ₁, hβ₂]
  · ext1; exact hα₁
  · ext1; exact hα₂

end

end GroundTheory.Heights₂.Heights.Model
