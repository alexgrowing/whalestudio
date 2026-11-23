import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFlatBaseChangeAffineMilnorSquareOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleOneOnThickeningStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_pic_of_glue_units {X X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ X) (p₂ : X₂ ⟶ X) [IsClosedImmersion p₂]
    [Surjective p₂] (D : LB X₂) (hD : D.IsLB)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU p₁ W a = pullU p₁ W b → pullU p₂ W a = pullU p₂ W b → a = b)
    (glue : ∀ (W : X.Opens) (a b : D.ι) (h : p₂ ⁻¹ᵁ W ≤ D.U a ⊓ D.U b),
      ∃ v : Γ(X, W)ˣ, pullU p₁ W v = 1 ∧ pullU p₂ W v = res h (D.g a b)) :
    ∃ c : Pic X, GlobalTheory.CechPic.pull p₁ c = 0 ∧ GlobalTheory.CechPic.pull p₂ c = cls D hD := by
  have hW : ∀ a : D.ι, ∃ W : X.Opens, ∀ y : X₂, p₂ y ∈ W ↔ y ∈ D.U a := fun a => by
    obtain ⟨t, ht, e⟩ := (p₂.isClosedEmbedding.isInducing.isOpen_iff).1 (D.U a).isOpen
    exact ⟨⟨t, ht⟩, fun y => Set.ext_iff.1 e y⟩
  choose W hW using hW
  have hle : ∀ a b, p₂ ⁻¹ᵁ (W a ⊓ W b) ≤ D.U a ⊓ D.U b := fun a b y hy => ⟨(hW a y).1 hy.1, (hW b y).1 hy.2⟩
  choose v hv₁ hv₂ using fun a b => glue (W a ⊓ W b) a b (hle a b)
  have g₁ : ∀ (y : X₁) a b, p₁ y ∈ W a → p₁ y ∈ W b → gm (𝟙 X₁ ≫ p₁) y (W a ⊓ W b) (v a b) = 1 :=
    fun y a b ha hb => by
      rw [← gm_pull (𝟙 X₁) p₁ y (W a ⊓ W b) ⟨ha, hb⟩, hv₁, map_one]
  have g₂ : ∀ (y : X₂) a b, p₂ y ∈ W a → p₂ y ∈ W b →
      gm (𝟙 X₂ ≫ p₂) y (W a ⊓ W b) (v a b) = gm (𝟙 X₂) y _ (D.g a b) :=
    fun y a b ha hb => by
      rw [← gm_pull (𝟙 X₂) p₂ y (W a ⊓ W b) ⟨ha, hb⟩, hv₂, gm_res (𝟙 X₂) y (hle a b) ⟨ha, hb⟩]
  have ext : ∀ (V : X.Opens) (a b : Γ(X, V)ˣ),
      (∀ y : X₁, p₁ y ∈ V → gm (𝟙 X₁ ≫ p₁) y V a = gm (𝟙 X₁ ≫ p₁) y V b) →
      (∀ y : X₂, p₂ y ∈ V → gm (𝟙 X₂ ≫ p₂) y V a = gm (𝟙 X₂ ≫ p₂) y V b) → a = b := fun V a b h₁ h₂ =>
    inj V a b
      (unit_ext fun y hy => by rw [gm_pull (𝟙 X₁) p₁ y V hy, gm_pull (𝟙 X₁) p₁ y V hy]; exact h₁ y hy)
      (unit_ext fun y hy => by rw [gm_pull (𝟙 X₂) p₂ y V hy, gm_pull (𝟙 X₂) p₂ y V hy]; exact h₂ y hy)
  let E : LB X := ⟨D.ι, W, v⟩
  have hE : E.IsLB :=
    { cover := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, rfl⟩ := Surjective.surj (f := p₂) x
        obtain ⟨a, ha⟩ := exists_chart hD y
        exact Opens.mem_iSup.2 ⟨a, (hW a y).2 ha⟩
      g_self := fun a => ext _ _ _
        (fun y hy => by
          rw [gm_res (𝟙 X₁ ≫ p₁) y _ hy, map_one]
          exact g₁ y a a hy hy)
        (fun y hy => by
          rw [gm_res (𝟙 X₂ ≫ p₂) y _ hy, map_one]
          exact (g₂ y a a hy hy).trans (gm_self hD (𝟙 X₂) y ((hW a y).1 hy)))
      cocycle := fun a b c => ext _ _ _
        (fun y hy => by
          rw [map_mul, gm_res (𝟙 X₁ ≫ p₁) y _ hy, gm_res (𝟙 X₁ ≫ p₁) y _ hy, gm_res (𝟙 X₁ ≫ p₁) y _ hy]
          exact (congrArg₂ (· * ·) (g₁ y a b hy.1.1 hy.1.2) (g₁ y b c hy.1.2 hy.2)).trans
            ((_root_.mul_one _).trans (g₁ y a c hy.1.1 hy.2).symm))
        (fun y hy => by
          rw [map_mul, gm_res (𝟙 X₂ ≫ p₂) y _ hy, gm_res (𝟙 X₂ ≫ p₂) y _ hy, gm_res (𝟙 X₂ ≫ p₂) y _ hy]
          exact (congrArg₂ (· * ·) (g₂ y a b hy.1.1 hy.1.2) (g₂ y b c hy.1.2 hy.2)).trans
            ((gm_cocycle hD (𝟙 X₂) y ((hW a y).1 hy.1.1) ((hW b y).1 hy.1.2) ((hW c y).1 hy.2)).trans
              (g₂ y a c hy.1.1 hy.2).symm)) }
  refine ⟨cls E hE, ?_, ?_⟩
  · rw [← cls_pull hE p₁ (pull_isLB hE p₁), cls_eq_zero_iff]
    refine ⟨⟨fun _ => 1⟩, (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩
    rw [map_one, map_one, _root_.mul_one]
    exact ((gm_pull_g E p₁ (𝟙 _) y J J' hJ hJ').trans (g₁ y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ'))).symm
  · rw [← cls_pull hE p₂ (pull_isLB hE p₂)]
    refine Eq.symm ((cls_eq_iff hD (pull_isLB hE p₂)).2 (iso_of_chart (pull_isLB hE p₂) ?_))
    exact
      { idx := fun a _ => a
        le := fun a y hy => mem_pull.2 ((hW a y).2 hy)
        g := fun y a b ha hb => Eq.symm ((gm_pull_g E p₂ (𝟙 _) y (fun _ => a) (fun _ => b)
          (mem_pull.2 ((hW a y).2 ha)) (mem_pull.2 ((hW b y).2 hb))).trans
          (g₂ y a b ((hW a y).2 ha) ((hW b y).2 hb))) }

theorem isPullback_whiskerLeft_left {S : Scheme.{0}} (A : Over S) {T T' : Over S} (j : T' ⟶ T) :
    IsPullback (A ◁ j).left (snd A T').left (snd A T).left j.left := by
  have P : IsPullback (A ◁ j) (snd A T') (snd A T) j := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst A T) s.snd) ?_ ?_ ?_⟩⟩
    · intro s
      ext <;> simp [s.condition]
    · intro s
      simp
    · intro s m h₁ h₂
      ext <;> simp [← h₁, ← h₂]
  exact P.map (Over.forget S)

theorem exists_pic_extend_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → IsClosedImmersion j₂.left → Surjective j₂.left → Surjective k₂.left → ∀ c₂ : Pic (A ⊗ T₂).left, GlobalTheory.CechPic.pull (A ◁ k₂).left c₂ = 0 → ∃ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 ∧ GlobalTheory.CechPic.pull (A ◁ j₂).left c = c₂ := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ hM hj hj' hk' c₂ hc
  have hk := hM.closed
  haveI : IsClosedImmersion (A ◁ j₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A j₂).flip hj
  haveI : Surjective (A ◁ j₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A j₂).flip hj'
  haveI : IsClosedImmersion (A ◁ k₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A k₂).flip hk
  haveI : Surjective (A ◁ k₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A k₂).flip hk'
  have w₀ : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext hM.w
  have w : (A ◁ k₁).left ≫ (A ◁ j₁).left = (A ◁ k₂).left ≫ (A ◁ j₂).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, w₀]
  obtain ⟨D, hD, rfl, h1⟩ := GlobalTheory.T.exists_cechCocycle_one_on_thickening _ _ (A ◁ k₂).left c₂ hc
  have H := GlobalTheory.T.sections_flat_baseChange_affineMilnorSquare_open S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
  generalize (A ◁ j₁).left = p₁ at *
  generalize (A ◁ j₂).left = p₂ at *
  generalize (A ◁ k₁).left = q₁ at *
  generalize (A ◁ k₂).left = q₂ at *
  have inj : ∀ (W : (A ⊗ T).left.Opens) (a b : Γ((A ⊗ T).left, W)ˣ), pullU p₁ W a = pullU p₁ W b →
      pullU p₂ W a = pullU p₂ W b → a = b := fun W a b h₁ h₂ =>
    Units.ext ((H W).1 _ _ (congrArg Units.val h₁) (congrArg Units.val h₂))
  refine exists_pic_of_glue_units p₁ p₂ D hD inj fun W a b h => ?_
  have e : q₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W) = q₂ ⁻¹ᵁ (p₂ ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have lift : ∀ u : Γ((A ⊗ T₂).left, p₂ ⁻¹ᵁ W)ˣ, pullU q₂ _ u = 1 →
      ∃ s : Γ((A ⊗ T).left, W), p₁.app W s = 1 ∧ p₂.app W s = u.val := fun u hu =>
    (H W).2 _ e.ge le_rfl e.le 1 u.val (by
      rw [map_one, Scheme.Hom.appLE_eq_app]
      exact (congrArg Units.val hu).symm)
  have hu : pullU q₂ _ (res h (D.g a b)) = 1 := unit_ext fun y hy => by
    rw [gm_pull (𝟙 _) q₂ y _ hy, gm_res (𝟙 _ ≫ q₂) y h hy, ← gm_pull (𝟙 _) q₂ y _ (h hy), h1, map_one, map_one]
  obtain ⟨s, hs₁, hs₂⟩ := lift _ hu
  obtain ⟨t, ht₁, ht₂⟩ := lift (res h (D.g a b))⁻¹ (by rw [map_inv, hu, inv_one])
  have st : s * t = 1 := (H W).1 _ _ (by rw [map_mul, hs₁, ht₁, map_one, _root_.mul_one])
    (by rw [map_mul, hs₂, ht₂, map_one, Units.mul_inv])
  exact ⟨⟨s, t, st, (mul_comm _ _).trans st⟩, Units.ext hs₁, Units.ext hs₂⟩

end GlobalTheory.DualOpen
