import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomPairDescendsToFinite
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolIsoDescent

open GlobalTheory.Spread GlobalTheory.HomPairDescent

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem model_descends : ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K), (∀ z : K, ∃ f : Polynomial k, f ≠ 0 ∧ Polynomial.eval₂ σ z f = 0) → ∀ (B₁ B₂ : PolAV (Sp k)) (P₀ : PolAV (Sp K)) (c₁ : P₀.A.left ⟶ B₁.A.left) (c₂ : P₀.A.left ⟶ B₂.A.left), IsGrpPullback P₀.A B₁.A (spMap σ) c₁ → IsGrpPullback P₀.A B₂.A (spMap σ) c₂ → LBIso P₀.L (B₁.L.pull c₁) → LBIso P₀.L (B₂.L.pull c₂) → ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (C : PolAV (Sp k₁)) (χ : C.A.left ⟶ B₁.A.left), IsGrpPullback C.A B₁.A (spMap α) χ → LBIso C.L (B₁.L.pull χ) → ∃ χ₂ : C.A.left ⟶ B₂.A.left, IsGrpPullback C.A B₂.A (spMap α) χ₂ ∧ LBIso C.L (B₂.L.pull χ₂) ∧ ∀ d : P₀.A.left ⟶ C.A.left, d ≫ χ = c₁ → d ≫ C.A.hom = P₀.A.hom ≫ spMap β → d ≫ χ₂ = c₂ := by
  classical
  intro k K _ _ σ hσ B₁ B₂ P₀ c₁ c₂ h₁ h₂ hL₁ hL₂
  letI : Algebra k K := σ.toAlgebra
  haveI := B₁.isAb.proper
  haveI := B₂.isAb.proper
  haveI := B₁.isAb.smooth
  haveI := B₂.isAb.smooth
  have g₁ : IsGrpPullback ((Over.pullback (spMap (algebraMap k K))).obj B₁.A) B₁.A (spMap σ) (pullback.fst _ _) :=
    isGrpPullback_pullback B₁.A (spMap σ)
  have g₂ : IsGrpPullback ((Over.pullback (spMap (algebraMap k K))).obj B₂.A) B₂.A (spMap σ) (pullback.fst _ _) :=
    isGrpPullback_pullback B₂.A (spMap σ)
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso h₁ g₁
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso h₂ g₂
  let f := e₁.inv ≫ e₂.hom
  let r := e₂.inv ≫ e₁.hom
  have mf : IsMonHom f := inferInstance
  obtain ⟨sf, hsf⟩ := exists_descend B₁.A B₂.A f
  obtain ⟨sr, hsr⟩ := exists_descend B₂.A B₁.A r
  let L₁ : IntermediateField k K := IntermediateField.adjoin k ((sf ∪ sr : Finset K) : Set K)
  have hL : ((sf ∪ sr : Finset K) : Set K) ⊆ L₁ := IntermediateField.subset_adjoin _ _
  obtain ⟨θf, hθf⟩ := hsf L₁ ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨θr, hθr⟩ := hsr L₁ ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have gA := isGrpPullback_bcMap B₁.A L₁.val
  have gB := isGrpPullback_bcMap B₂.A L₁.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L₁ K L₁.val.toRingHom
  haveI := (hepi _ _ _ _ _ gA.1).1
  haveI := (hepi _ _ _ _ _ gB.1).1
  haveI mθ : IsMonHom θf := (hmon _ _ _ _ _ _ θf f gA gB hθf).1 mf
  have r1 : θf ≫ θr = 𝟙 _ := by
    have := comp_eq_pow_of_epi gA hθf hθr 1 (by rw [pow_one]; simp [f, r])
    rwa [pow_one] at this
  have r2 : θr ≫ θf = 𝟙 _ := by
    have := comp_eq_pow_of_epi gB hθr hθf 1 (by rw [pow_one]; simp [f, r])
    rwa [pow_one] at this
  let θ : (Over.pullback (spMap (algebraMap k L₁))).obj B₁.A ≅ (Over.pullback (spMap (algebraMap k L₁))).obj B₂.A :=
    ⟨θf, θr, r1, r2⟩
  haveI : IsMonHom θ.hom := mθ
  haveI := m₁
  let φP : P₀.A.left ⟶ ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A).left :=
    e₁.hom.left ≫ bcMap B₁.A.hom L₁.val
  have hφP : IsGrpPullback P₀.A ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) (spMap L₁.val.toRingHom) φP :=
    ((isGrpPullback_of_iso e₁).comp gA).congr (Category.id_comp _) rfl
  have hfst : φP ≫ pullback.fst _ _ = c₁ := by
    simp only [φP, Category.assoc, bcMap_fst]; exact he₁
  have hc₂ : φP ≫ θf.left ≫ pullback.fst _ _ = c₂ := by
    simp only [φP, Category.assoc]
    rw [reassoc_of% hθf, bcMap_fst]
    show e₁.hom.left ≫ (e₁.inv ≫ e₂.hom).left ≫ _ = _
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id_assoc, he₂]
  have HP : LBIso (B₁.L.pull c₁) (B₂.L.pull c₂) :=
    LBIso.trans (pull_isLB B₁.isLB c₁) P₀.isLB (pull_isLB B₂.isLB c₂) hL₁.symm hL₂
  have HX := LBIso.chartPull
    (chartPullOut B₁.L (fun _ => pullback.fst B₁.A.hom (spMap (algebraMap k L₁))) (fun _ => 1) φP (fun _ => c₁)
      (fun _ => hfst.symm))
    (chartPullOut B₂.L (fun _ => θf.left ≫ pullback.fst B₂.A.hom (spMap (algebraMap k L₁))) (fun _ => 1) φP
      (fun _ => c₂) (fun _ => hc₂.symm)) HP
  obtain ⟨s₂, hs₂⟩ := lbIso_descends_to_subfield_containing_finset L₁ K L₁.val.toRingHom
    ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) P₀.A φP
    (B₁.L.pull (pullback.fst B₁.A.hom (spMap (algebraMap k L₁))))
    (B₂.L.pull (θf.left ≫ pullback.fst B₂.A.hom (spMap (algebraMap k L₁)))) hφP.1
    (by change QuasiCompact (pullback.snd _ _); infer_instance)
    (by change QuasiSeparated (pullback.snd _ _); infer_instance) (pull_isLB B₁.isLB _) (pull_isLB B₂.isLB _) HX
  refine ⟨sf ∪ sr ∪ s₂, ?_⟩
  intro k₁ _ α β hαβ hs C χ hχ hCL
  let E : IntermediateField k K :=
    { β.fieldRange with algebraMap_mem' := fun r => RingHom.mem_fieldRange.2 ⟨α r, RingHom.congr_fun hαβ r⟩ }
  have hle : L₁ ≤ E := IntermediateField.adjoin_le_iff.2 fun x hx => by
    obtain ⟨y, hy⟩ := hs (Finset.coe_subset.2 Finset.subset_union_left hx)
    exact RingHom.mem_fieldRange.2 ⟨y, hy⟩
  have hran : ∀ x : L₁, ∃ y, β y = x := fun x => RingHom.mem_fieldRange.1 (hle x.2)
  choose ρ₀ hρ₀ using hran
  let α₁ : L₁ →+* k₁ :=
    { toFun := ρ₀
      map_one' := β.injective (by simp [hρ₀])
      map_mul' := fun x y ↦ β.injective (by simp [hρ₀])
      map_zero' := β.injective (by simp [hρ₀])
      map_add' := fun x y ↦ β.injective (by simp [hρ₀]) }
  have hα₁β : β.comp α₁ = L₁.val.toRingHom := RingHom.ext fun x => hρ₀ x
  have hα₁ : α₁.comp (algebraMap k L₁) = α := RingHom.ext fun r => β.injective
    ((hρ₀ _).trans (RingHom.congr_fun hαβ r).symm)
  have hsp : spMap α₁ ≫ spMap (algebraMap k L₁) = spMap α := by rw [spMap_comp', hα₁]
  have hw : χ ≫ B₁.A.hom = (C.A.hom ≫ spMap α₁) ≫ spMap (algebraMap k L₁) := by
    rw [hχ.1.w, Category.assoc, hsp]
  let j : C.A.left ⟶ ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A).left := pullback.lift χ (C.A.hom ≫ spMap α₁) hw
  have hj₁ : j ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = C.A.hom ≫ spMap α₁ := pullback.lift_snd _ _ _
  have hj : IsGrpPullback C.A ((Over.pullback (spMap (algebraMap k L₁))).obj B₁.A) (spMap α₁) j :=
    (isGrpPullback_pullback B₁.A _).cancel (hχ.congr hsp.symm hj₁.symm) hj₂
  refine ⟨j ≫ θf.left ≫ pullback.fst _ _, ?_, ?_, ?_⟩
  · exact (hj.comp ((isGrpPullback_of_iso θ).comp (isGrpPullback_pullback B₂.A _))).congr
      (by rw [Category.id_comp, hsp]) rfl
  · have H := hs₂ k₁ α₁ β hα₁β ((Finset.coe_subset.2 Finset.subset_union_right).trans hs) C.A j hj.1
    have H' : LBIso (B₁.L.pull χ) (B₂.L.pull (j ≫ θf.left ≫ pullback.fst _ _)) :=
      LBIso.chartPull
        (chartPullSame B₁.L (fun _ => χ) (fun _ => j ≫ pullback.fst _ _) (fun _ => 1) (𝟙 _)
          (fun _ => by rw [Category.id_comp, hj₁]))
        (chartPullSame B₂.L (fun _ => j ≫ θf.left ≫ pullback.fst _ _) (fun _ => j ≫ θf.left ≫ pullback.fst _ _)
          (fun _ => 1) (𝟙 _) (fun _ => by rw [Category.id_comp]))
        (LBIso.chartPull (chartPullIn B₁.L (fun _ => pullback.fst _ _) (fun _ => 1) j)
          (chartPullIn B₂.L (fun _ => θf.left ≫ pullback.fst _ _) (fun _ => 1) j) H)
    exact LBIso.trans C.isLB (pull_isLB B₁.isLB _) (pull_isLB B₂.isLB _) hCL H'
  · intro d hd₁ hd₂
    have hdj : d ≫ j = φP := by
      apply pullback.hom_ext
      · rw [Category.assoc, hj₁, hd₁, hfst]
      · rw [Category.assoc, hj₂, ← Category.assoc, hd₂, Category.assoc, spMap_comp', hα₁β]
        exact hφP.1.w.symm
    rw [reassoc_of% hdj]
    exact hc₂

end GlobalTheory.PolIsoDescent
