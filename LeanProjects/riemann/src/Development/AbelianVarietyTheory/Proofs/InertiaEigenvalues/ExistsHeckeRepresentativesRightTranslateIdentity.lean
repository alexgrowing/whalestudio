import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOfCfEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.UpInj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levW_le_GfC (R : RealDat D A Ks) (i : Fin D.R.m) {k : GA D (Wc D i)} (hk : k ∈ levW R i) :
    k ∈ GfC (Wc D i) := hk.1

theorem mem_locK_iff (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC (Wc D i)) :
    (g : GA D (Wc D i)) ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} ↔
      g ∈ KR R i ∧ cf (Wc D i) v g = g := by
  simp only [Set.mem_setOf_eq, KR, Subgroup.mem_subgroupOf, cf_eq_self_iff]

theorem dcRep_exists (R : RealDat D A Ks) (i : Fin D.R.m) (hT : TransLaws R i)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i)) (hα : cf (Wc D i) v α = α) :
    ∃ C, DCRep (cf (Wc D i) v) (KR R i) α C := by
  classical
  obtain ⟨C, hsupp, hrep⟩ := hT.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα)
  refine ⟨C.subtype (· ∈ GfC (Wc D i)), fun δ hδ => ?_, fun x ⟨k₁, k₂, h1, h2, h3, h4, hx⟩ => ?_⟩
  · rw [Finset.mem_subtype] at hδ
    refine ⟨(cf_eq_self_iff _ v δ).2 (hsupp _ hδ), ?_⟩
    obtain ⟨-, k₁, hk₁, k₂, hk₂, he⟩ := hrep.1 _ hδ
    refine ⟨⟨k₁, levW_le_GfC R i hk₁.1⟩, ⟨k₂, levW_le_GfC R i hk₂.1⟩, ?_⟩
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, levW_le_GfC R i hk₁.1⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, levW_le_GfC R i hk₂.1⟩).1 hk₂
    exact ⟨a1, a2, b1, b2, Subtype.ext he⟩
  · have hk₁ := (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩
    have hk₂ := (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩
    have hx' : (x : GA D (Wc D i)) = (k₁ : GA D (Wc D i)) * α * k₂ := by rw [hx]; rfl
    obtain ⟨γ, ⟨hγC, hγK⟩, huniq⟩ := hrep.2 x ⟨_, hk₁, _, hk₂, hx'⟩
    have hγG : γ ∈ GfC (Wc D i) := (hrep.1 γ hγC).1
    have e : ((⟨γ, hγG⟩⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = γ⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm := (mem_locK_iff R i v (⟨γ, hγG⟩⁻¹ * x)).1 (by rw [e]; exact hγK)
    refine ⟨⟨γ, hγG⟩, ⟨Finset.mem_subtype.2 hγC, hm⟩, ?_⟩
    rintro δ ⟨hδC, hδK, hδc⟩
    have e' : ((δ⁻¹ * x : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * (x : GA D (Wc D i)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hm' := (mem_locK_iff R i v (δ⁻¹ * x)).2 ⟨hδK, hδc⟩
    rw [e'] at hm'
    exact Subtype.ext (huniq (δ : GA D (Wc D i)) ⟨Finset.mem_subtype.1 hδC, hm'⟩)

theorem isCosetRep_map (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GfC (Wc D i))
    (C : Finset (GfC (Wc D i))) (hC : DCRep (cf (Wc D i) v) (KR R i) α C) :
    (∀ γ ∈ C.map (Function.Embedding.subtype _), SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (GlobalTheory.LevelProduct.fE D v) k} α
        (C.map (Function.Embedding.subtype _)) := by
  classical
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_, fun x ⟨k₁, hk₁, k₂, hk₂, hx⟩ => ?_⟩
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    exact (cf_eq_self_iff _ v δ).1 (hC.1 δ hδ).1
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_map.1 hγ
    obtain ⟨-, k₁, k₂, h1, h2, h3, h4, he⟩ := hC.1 δ hδ
    refine ⟨δ.2, k₁, (mem_locK_iff R i v k₁).2 ⟨h1, h2⟩, k₂, (mem_locK_iff R i v k₂).2 ⟨h3, h4⟩, ?_⟩
    simp [he]
  · have g₁ := levW_le_GfC R i hk₁.1
    have g₂ := levW_le_GfC R i hk₂.1
    have hxG : x ∈ GfC (Wc D i) := by
      rw [hx]; exact (GfC (Wc D i)).mul_mem ((GfC (Wc D i)).mul_mem g₁ α.2) g₂
    obtain ⟨a1, a2⟩ := (mem_locK_iff R i v ⟨k₁, g₁⟩).1 hk₁
    obtain ⟨b1, b2⟩ := (mem_locK_iff R i v ⟨k₂, g₂⟩).1 hk₂
    have hx2 : (⟨x, hxG⟩ : GfC (Wc D i)) = ⟨k₁, g₁⟩ * α * ⟨k₂, g₂⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hx
    have hex := hC.2 ⟨x, hxG⟩ ⟨_, _, a1, a2, b1, b2, hx2⟩
    obtain ⟨δ, ⟨hδC, hδK, hδc⟩, huniq⟩ := hex
    have hm := (mem_locK_iff R i v (δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).2 ⟨hδK, hδc⟩
    have e : ((δ⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e] at hm
    refine ⟨(δ : GA D (Wc D i)), ⟨Finset.mem_map_of_mem _ hδC, hm⟩, ?_⟩
    rintro γ ⟨hγC, hγK⟩
    obtain ⟨δ', hδ', rfl⟩ := Finset.mem_map.1 hγC
    have e' : ((δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)) : GfC (Wc D i)) : GA D (Wc D i)) = (δ' : GA D (Wc D i))⁻¹ * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨c1, c2⟩ := (mem_locK_iff R i v (δ'⁻¹ * (⟨x, hxG⟩ : GfC (Wc D i)))).1 (by rw [e']; exact hγK)
    exact congrArg Subtype.val (huniq δ' ⟨hδ', c1, c2⟩)

theorem heckeReps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m),
    TransLaws R i → ∀ (B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)),
    (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) →
    (∀ v α, GlobalTheory.UpInj.cf (Wc D i) v α = α → ∃ C, GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C) ∧
    (∀ v α C, GlobalTheory.UpInj.cf (Wc D i) v α = α → GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C →
      ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hT B hB
  refine ⟨fun v α hα => dcRep_exists R i hT v α hα, fun v α C hα hC γ => ?_⟩
  obtain ⟨hs, hr⟩ := isCosetRep_map R i v α C hC
  have hB1 : ∀ y, B 1 y = y := fun y => ext_inner_left ℂ fun x => by
    rw [← hB, OneMemClass.coe_one, hT.2.2.2.2.2]
  have key : ∀ (γ : GfC (Wc D i)) y y', (∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' =
      ∑ δ ∈ C.map (Function.Embedding.subtype _), trPair R i (γ * δ) x y) →
      B γ y' = (∑ δ ∈ C, B (γ * δ)) y := fun γ y y' h => ext_inner_left ℂ fun x => by
    rw [← hB, h γ γ.2 x, Finset.sum_map, ContinuousLinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← hB]; rfl
  ext y
  obtain ⟨y', -, hy'⟩ := hT.2.1 v _ (isFinIdem_fE v) α ((cf_eq_self_iff _ v α).1 hα) _ hs hr y
  have e1 := key 1 y y' hy'
  simp only [one_mul, hB1] at e1
  rw [ContinuousLinearMap.mul_apply, ← e1, key γ y y' hy']

end GlobalTheory.UpInj

end
