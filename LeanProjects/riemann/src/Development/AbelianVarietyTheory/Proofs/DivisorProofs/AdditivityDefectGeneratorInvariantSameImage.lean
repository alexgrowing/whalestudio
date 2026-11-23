import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

private theorem coe_gm_eq_stalkMap_germ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U)
    (a : Γ(X, U)ˣ) :
    ((gm f y U a : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) =
      f.stalkMap y (X.presheaf.germ U (f y) h (a : Γ(X, U))) := by
  unfold gm
  rw [dif_pos h]
  simp only [pullU, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

private theorem gm_res_pullU_lemma_2 {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (ψ : Z ⟶ Y) (z : Z) (U : X.Opens)
    {V : Y.Opens} (hle : V ≤ φ ⁻¹ᵁ U) (hz : ψ z ∈ V) (a : Γ(X, U)ˣ) :
    gm ψ z V (res hle (pullU φ U a)) = gm (ψ ≫ φ) z U a := by
  have h1 : φ (ψ z) ∈ U := hle hz
  apply Units.ext
  rw [coe_gm_eq_stalkMap_germ ψ z V hz, coe_gm_eq_stalkMap_germ (ψ ≫ φ) z U h1]
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [Scheme.Hom.stalkMap_comp]
  erw [TopCat.Presheaf.germ_res_apply]
  exact congrArg (Scheme.Hom.stalkMap ψ z) (Scheme.Hom.germ_stalkMap_apply φ U (ψ z) h1 _).symm

private theorem gm_pullTop_inv {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (a : Γ(X, ⊤)ˣ) :
    gm f z ⊤ (pullTop g a) = gm (f ≫ g) z ⊤ a := by
  apply Units.ext
  rw [coe_gm_eq_stalkMap_germ f z ⊤ trivial, coe_gm_eq_stalkMap_germ (f ≫ g) z ⊤ trivial]
  rw [Scheme.Hom.stalkMap_comp]
  exact congrArg (Scheme.Hom.stalkMap f z) (Scheme.Hom.germ_stalkMap_apply g ⊤ (f z) trivial _).symm

theorem gm_character_mul {S : Scheme.{0}} {N T Z : Over S} [GrpObj N] {χ : Γ((N ⊗ T).left, ⊤)ˣ}
    (hχ : IsCharacter χ) (ν₁ ν₂ : Z ⟶ N) (t : Z ⟶ T) (z : Z.left) :
    gm (lift (ν₁ * ν₂) t).left z ⊤ χ = gm (lift ν₁ t).left z ⊤ χ * gm (lift ν₂ t).left z ⊤ χ := by
  have hy1 : lift ν₁ (lift ν₂ t) ≫ lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T) =
      lift (ν₁ * ν₂) t := by
    simp [comp_lift, MonObj.comp_mul]
  have hy2 : lift ν₁ (lift ν₂ t) ≫ lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T) = lift ν₁ t := by
    simp [comp_lift]
  have hy3 : lift ν₁ (lift ν₂ t) ≫ snd N (N ⊗ T) = lift ν₂ t := by simp
  have hc : IsCharacter χ := hχ
  unfold IsCharacter at hc
  rw [← hy1, Over.comp_left, ← gm_pullTop_inv, hc, map_mul, gm_pullTop_inv, gm_pullTop_inv,
    ← Over.comp_left, ← Over.comp_left, hy2, hy3]

theorem gm_equivGen {S : Scheme.{0}} {A A' N T Z : Over S} [GrpObj A] {i : N ⟶ A} {q : A ⟶ A'}
    {χ : Γ((N ⊗ T).left, ⊤)ˣ} {M : LB (A' ⊗ T).left} {e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ}
    (he : IsEquivGen i q χ M e) (a b : Z ⟶ A) (ν : Z ⟶ N) (t : Z ⟶ T) (hb : b = a * (ν ≫ i)) (z : Z.left)
    (k : M.ι) (h₁ : (lift b t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U k)
    (h₂ : (lift a t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U k) :
    gm (lift b t).left z _ (e k) = gm (lift ν t).left z ⊤ χ * gm (lift a t).left z _ (e k) := by
  set y : Z ⟶ A ⊗ (N ⊗ T) := lift a (lift ν t) with hy
  have e1 : y.left ≫ (actMap i T).left = (lift b t).left := by
    rw [← Over.comp_left, hb, hy]
    unfold actMap
    simp [comp_lift, MonObj.comp_mul]
  have e2 : y.left ≫ (prMap A N T).left = (lift a t).left := by
    rw [← Over.comp_left, hy]
    unfold prMap
    simp [comp_lift]
  have e3 : y.left ≫ (snd A (N ⊗ T)).left = (lift ν t).left := by
    rw [← Over.comp_left, hy]
    simp
  have w1 : y.left z ∈ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := by
    rw [← e1] at h₁
    exact h₁
  have w2 : y.left z ∈ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := by
    rw [← e2] at h₂
    exact h₂
  have key := congrArg (gm y.left z ((actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
    (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))) (he.2 k _ inf_le_left inf_le_right)
  have hw : y.left z ∈ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
      (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := ⟨w1, w2⟩
  rw [map_mul, gm_res_pullU_lemma_2 _ _ _ _ _ hw, gm_res_pullU_lemma_2 _ _ _ _ _ hw, e1, e2] at key
  have hχ' : gm y.left z ((actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
      (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)) (res le_top (pullTop (snd A (N ⊗ T)).left χ)) =
      gm (lift ν t).left z ⊤ χ := by
    have := gm_res_pullU_lemma_2 (snd A (N ⊗ T)).left y.left z ⊤ (V := _) le_top hw χ
    rw [e3] at this
    exact this
  rw [hχ'] at key
  exact key

theorem gm_addGen {S : Scheme.{0}} {A A' T Z : Over S} [GrpObj A] [GrpObj A'] (q : A ⟶ A') [IsMonHom q]
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (a a' : Z ⟶ A) (t : Z ⟶ T)
    (z : Z.left) (k : (addBundle M).ι)
    (h : (lift a (lift a' t)).left z ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k) :
    ((lift a t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit) ∧
      (lift a' t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit) ∧
      (lift (a * a') t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) ∧
    gm (lift a (lift a' t)).left z _ (addGen q M e k) =
      gm (lift a t).left z _ (e (k.1.1 PUnit.unit)) * gm (lift a' t).left z _ (e (k.1.2 PUnit.unit)) *
        (gm (lift (a * a') t).left z _ (e (k.2 PUnit.unit)))⁻¹ := by
  set y : Z ⟶ A ⊗ (A ⊗ T) := lift a (lift a' t) with hy
  have eF : y.left ≫ (ptFst A T).left = (lift a t).left := by
    rw [← Over.comp_left, hy]
    unfold ptFst
    simp [comp_lift]
  have eS : y.left ≫ (ptSnd A T).left = (lift a' t).left := by
    rw [← Over.comp_left, hy]
    unfold ptSnd
    simp [comp_lift]
  have eM : y.left ≫ (ptMul A T).left = (lift (a * a') t).left := by
    rw [← Over.comp_left, hy]
    unfold ptMul
    simp [comp_lift, MonObj.comp_mul]
  have m1 := addGen_le₁ q M k h
  have m2 := addGen_le₂ q M k h
  have m3 := addGen_le₃ q M k h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← eF]
    exact m1
  · rw [← eS]
    exact m2
  · rw [← eM]
    exact m3
  · unfold addGen
    rw [map_mul, map_mul, map_inv, gm_res_pullU_lemma_2 _ _ _ _ _ h, gm_res_pullU_lemma_2 _ _ _ _ _ h,
      gm_res_pullU_lemma_2 _ _ _ _ _ h, eF, eS, eM]

private theorem germ_eq_gm_coe {Z : Scheme.{0}} (W : Z.Opens) (w : Z) (hw : w ∈ W) (x : Γ(Z, W)ˣ) :
    Z.presheaf.germ W w hw (x : Γ(Z, W)) = ((gm (𝟙 Z) w W x : (Z.presheaf.stalk w)ˣ) : Z.presheaf.stalk w) := by
  rw [coe_gm_eq_stalkMap_germ (𝟙 Z) w W hw]
  erw [Scheme.Hom.stalkMap_id]
  rfl

private theorem mul_mul_mul_inv_cancel_left_factors {G : Type*} [CommGroup G] (c₁ c₂ E₁ E₂ E₃ : G) :
    c₁ * E₁ * (c₂ * E₂) * (c₁ * c₂ * E₃)⁻¹ = E₁ * E₂ * E₃⁻¹ := by
  rw [mul_inv (c₁ * c₂) E₃, _root_.mul_mul_mul_comm c₁ E₁ c₂ E₂, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]

theorem addGen_invariant : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsMonHom i → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → IsEquivGen i q χ M e → ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ (A ⊗ (A ⊗ T)).left), y₁ ≫ (pmap2 q T).left = y₂ ≫ (pmap2 q T).left → ∀ (k : (addBundle M).ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)), res h₁ (pullU y₁ _ (addGen q M e k)) = res h₂ (pullU y₂ _ (addGen q M e k)) := by
  intro S A A' N T _i1 _i2 _i3 _i4 i q _i5 χ M e hi hpb hχ he Z y₁ y₂ hy k W h₁ h₂
  haveI := hi
  apply Units.ext
  apply TopCat.Presheaf.section_ext Z.sheaf W
  intro w hw
  erw [germ_eq_gm_coe W w hw, germ_eq_gm_coe W w hw]
  rw [gm_res_pullU_lemma_2 y₁ (𝟙 Z) w _ h₁ hw, gm_res_pullU_lemma_2 y₂ (𝟙 Z) w _ h₂ hw, Category.id_comp,
    Category.id_comp]
  have m₁ : y₁ w ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k := h₁ hw
  have m₂ : y₂ w ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k := h₂ hw
  have hyS : y₂ ≫ (A ⊗ (A ⊗ T)).hom = y₁ ≫ (A ⊗ (A ⊗ T)).hom := by
    have h := congrArg (· ≫ (A' ⊗ (A' ⊗ T)).hom) hy
    simp only [Category.assoc, Over.w] at h
    exact h.symm
  let Z' : Over S := Over.mk (y₁ ≫ (A ⊗ (A ⊗ T)).hom)
  let Y₁ : Z' ⟶ A ⊗ (A ⊗ T) := Over.homMk y₁ rfl
  let Y₂ : Z' ⟶ A ⊗ (A ⊗ T) := Over.homMk y₂ hyS
  have hY : Y₁ ≫ pmap2 q T = Y₂ ≫ pmap2 q T := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    exact hy
  have h_a : Y₁ ≫ fst A (A ⊗ T) ≫ q = Y₂ ≫ fst A (A ⊗ T) ≫ q := by
    have h := congrArg (· ≫ fst A' (A' ⊗ T)) hY
    simpa [pmap2] using h
  have h_b : Y₁ ≫ snd A (A ⊗ T) ≫ fst A T ≫ q = Y₂ ≫ snd A (A ⊗ T) ≫ fst A T ≫ q := by
    have h := congrArg (· ≫ snd A' (A' ⊗ T) ≫ fst A' T) hY
    simpa [pmap2, pmap] using h
  have h_t : Y₁ ≫ snd A (A ⊗ T) ≫ snd A T = Y₂ ≫ snd A (A ⊗ T) ≫ snd A T := by
    have h := congrArg (· ≫ snd A' (A' ⊗ T) ≫ snd A' T) hY
    simpa [pmap2, pmap] using h
  have eY₁ : lift (Y₁ ≫ fst A (A ⊗ T)) (lift (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T)) = Y₁ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext <;> simp
  have eY₂ : lift (Y₂ ≫ fst A (A ⊗ T)) (lift (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T)) = Y₂ := by
    rw [h_t]
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext <;> simp
  have hP := pmap_isPullback_actMap S A A' N T i q hi inferInstance hpb
  have wa : lift (Y₁ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T =
      lift (Y₂ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T := by
    simp [pmap, comp_lift, h_a]
  have wb : lift (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T =
      lift (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T := by
    simp [pmap, comp_lift, h_b]
  have key : ∀ (a₁ a₂ : Z' ⟶ A) (t : Z' ⟶ T), lift a₁ t ≫ pmap q T = lift a₂ t ≫ pmap q T →
      ∃ ν : Z' ⟶ N, a₂ = a₁ * (ν ≫ i) := by
    intro a₁ a₂ t hw'
    have e1 := congrArg (· ≫ fst A T) (hP.lift_snd (lift a₁ t) (lift a₂ t) hw')
    have e2 := congrArg (· ≫ fst A T) (hP.lift_fst (lift a₁ t) (lift a₂ t) hw')
    generalize hP.lift (lift a₁ t) (lift a₂ t) hw' = u at e1 e2
    refine ⟨u ≫ snd A (N ⊗ T) ≫ fst N T, ?_⟩
    simp only [actMap, prMap, Category.assoc, lift_fst, MonObj.comp_mul] at e1 e2
    rw [← e1, e2]
    simp [Category.assoc]
  obtain ⟨ν, hν⟩ := key _ _ _ wa
  obtain ⟨ν', hν'⟩ := key _ _ _ wb
  have hνν : Y₂ ≫ fst A (A ⊗ T) * (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) =
      Y₁ ≫ fst A (A ⊗ T) * (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) * ((ν * ν') ≫ i) := by
    rw [hν, hν', MonObj.mul_comp, _root_.mul_mul_mul_comm]
  have M₁ := (gm_addGen q M e (Y₁ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T)
    (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) w k (by rw [eY₁]; exact m₁))
  have M₂ := (gm_addGen q M e (Y₂ ≫ fst A (A ⊗ T)) (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T)
    (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) w k (by rw [eY₂]; exact m₂))
  have G₁ := M₁.2
  have G₂ := M₂.2
  rw [eY₁] at G₁
  rw [eY₂] at G₂
  refine congrArg Units.val ?_
  change gm Y₁.left w _ (addGen q M e k) = gm Y₂.left w _ (addGen q M e k) at ⊢
  rw [G₁, G₂, gm_equivGen he _ _ ν _ hν w _ M₂.1.1 M₁.1.1, gm_equivGen he _ _ ν' _ hν' w _ M₂.1.2.1 M₁.1.2.1,
    gm_equivGen he _ _ (ν * ν') _ hνν w _ M₂.1.2.2 M₁.1.2.2, gm_character_mul hχ ν ν', mul_mul_mul_inv_cancel_left_factors]

end GlobalTheory.CharKer
