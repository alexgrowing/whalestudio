import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ProdFundDom

theorem isFundamentalDomain_prod {T L : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] [Group L] [MeasurableSpace L]
    (ΓT : Subgroup T) [DiscreteTopology ΓT] (ΓL : Subgroup L)
    (ν : Measure T) [SFinite ν] (μ₁ : Measure L) [SFinite μ₁] {𝓕₁ : Set L}
    (h₁ : IsFundamentalDomain ΓL 𝓕₁ μ₁) :
    IsFundamentalDomain (ΓT.prod ΓL) (AutomorphicL2Unitary.stdDom ΓT ×ˢ 𝓕₁) (ν.prod μ₁) where
  nullMeasurableSet := (AutomorphicL2Unitary.measurableSet_stdDom ΓT).nullMeasurableSet.prod h₁.nullMeasurableSet
  ae_covers := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae h₁.ae_covers] with p hp
    obtain ⟨γ, hγ⟩ := hp
    obtain ⟨δ, hδ, -⟩ := AutomorphicL2Unitary.existsUnique_stdDom ΓT p.1
    refine ⟨⟨((δ : T), (γ : L)), Subgroup.mem_prod.2 ⟨δ.2, γ.2⟩⟩, ?_, ?_⟩
    · simpa [Subgroup.smul_def] using hδ
    · simpa [Subgroup.smul_def] using hγ
  aedisjoint := by
    intro g h hgh
    have hg := Subgroup.mem_prod.1 g.2
    have hh := Subgroup.mem_prod.1 h.2
    by_cases h1 : (g : T × L).1 = (h : T × L).1
    · have h2 : (⟨(g : T × L).2, hg.2⟩ : ΓL) ≠ ⟨(h : T × L).2, hh.2⟩ := fun e =>
        hgh (Subtype.ext (Prod.ext h1 (congrArg Subtype.val e)))
      have h3 := h₁.aedisjoint h2
      refine measure_mono_null (t := univ ×ˢ ((⟨(g : T × L).2, hg.2⟩ : ΓL) • 𝓕₁ ∩
        (⟨(h : T × L).2, hh.2⟩ : ΓL) • 𝓕₁)) ?_ ?_
      · rintro x ⟨hx, hx'⟩
        rw [mem_smul_set_iff_inv_smul_mem] at hx hx'
        refine ⟨trivial, ?_, ?_⟩
        · rw [mem_smul_set_iff_inv_smul_mem]
          simpa [Subgroup.smul_def] using hx.2
        · rw [mem_smul_set_iff_inv_smul_mem]
          simpa [Subgroup.smul_def] using hx'.2
      · rw [Measure.prod_prod]
        exact mul_eq_zero_of_right _ h3
    · refine Disjoint.aedisjoint (disjoint_left.2 fun x hx hx' => h1 ?_)
      rw [mem_smul_set_iff_inv_smul_mem] at hx hx'
      have e := (AutomorphicL2Unitary.existsUnique_stdDom ΓT x.1).unique (y₁ := ⟨(g : T × L).1⁻¹, ΓT.inv_mem hg.1⟩)
        (y₂ := ⟨(h : T × L).1⁻¹, ΓT.inv_mem hh.1⟩) (by simpa [Subgroup.smul_def] using hx.1)
        (by simpa [Subgroup.smul_def] using hx'.1)
      simpa using congrArg Subtype.val e

end GlobalTheory.ProdFundDom

namespace GlobalTheory.ProdFundDom

theorem setIntegral_eq_zero_of_prod : ∀ (G T L : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T] [T2Space T]
    [MeasurableSpace T] [BorelSpace T]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L]
    (φ : T × L ≃ₜ* G) (Γ : Subgroup G) (ΓT : Subgroup T) (ΓL : Subgroup L) [DiscreteTopology ΓT],
    (∀ p : T × L, φ p ∈ Γ ↔ p.1 ∈ ΓT ∧ p.2 ∈ ΓL) →
    ∀ (A : G → ℂ) (a : L → ℂ), (∀ p : T × L, A (φ p) = a p.2) →
    (∀ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure → IsFundamentalDomain Γ 𝓕 μ →
      IntegrableOn A 𝓕 μ ∧ ∫ m in 𝓕, A m ∂μ = 0) →
    ∀ (μ₁ : Measure L) (𝓕₁ : Set L), μ₁.IsHaarMeasure → IsFundamentalDomain ΓL 𝓕₁ μ₁ →
      IntegrableOn a 𝓕₁ μ₁ ∧ ∫ m in 𝓕₁, a m ∂μ₁ = 0 := by
  intro G T L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ Γ ΓT ΓL _ hΓ A a hA hint μ₁ 𝓕₁ hμ₁ h₁
  let ν : Measure T := Measure.haar
  let e : (T × L) ≃ᵐ G := φ.toHomeomorph.toMeasurableEquiv
  let μ : Measure G := (ν.prod μ₁).map φ
  have he : MeasurePreserving e (ν.prod μ₁) μ := ⟨e.measurable, rfl⟩
  haveI : μ.IsHaarMeasure := MulEquiv.isHaarMeasure_map (ν.prod μ₁) φ.toMulEquiv φ.continuous φ.symm.continuous
  let D := AutomorphicL2Unitary.stdDom ΓT
  let S := D ×ˢ 𝓕₁
  have hF : IsFundamentalDomain Γ (e.symm ⁻¹' S) μ := by
    refine (isFundamentalDomain_prod ΓT ΓL ν μ₁ h₁).preimage_of_equiv
      (MeasurePreserving.symm e he).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hΓ γ).2 (Subgroup.mem_prod.1 γ.2)⟩) ⟨fun x y h => ?_, fun γ => ?_⟩ fun g x => ?_
    · exact Subtype.ext (φ.injective (congrArg Subtype.val h))
    · refine ⟨⟨φ.symm γ, Subgroup.mem_prod.2 ((hΓ _).1 (by simpa using γ.2))⟩, Subtype.ext (by simp)⟩
    · show φ.symm (φ g * x) = g * φ.symm x
      rw [map_mul, φ.symm_apply_apply]
  obtain ⟨hI0, hZ0⟩ := hint μ _ inferInstance hF
  have hpre : e ⁻¹' (e.symm ⁻¹' S) = S := by ext p; simp
  have hcomp : A ∘ e = fun p : T × L => a p.2 := funext fun p => hA p
  have hI1 : IntegrableOn (fun p : T × L => a p.2) S (ν.prod μ₁) := by
    rw [← hcomp, ← hpre]; exact (he.integrableOn_comp_preimage e.measurableEmbedding).2 hI0
  have hZ1 : ∫ p in S, a p.2 ∂(ν.prod μ₁) = 0 := by
    rw [← hZ0, ← he.setIntegral_preimage_emb e.measurableEmbedding, hpre]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => (hA p).symm)
  rw [IntegrableOn, ← Measure.prod_restrict] at hI1
  rw [← Measure.prod_restrict] at hZ1
  have hD0 : ν D ≠ 0 := (AutomorphicL2Unitary.isFundamentalDomain_stdDom ΓT ν).measure_ne_zero (NeZero.ne _)
  haveI : NeZero (ν.restrict D) := ⟨by rwa [Ne, Measure.restrict_eq_zero]⟩
  obtain ⟨_, hσ⟩ := hI1.prod_right_ae.exists
  refine ⟨hσ, ?_⟩
  rw [integral_fun_snd] at hZ1
  by_cases htop : ν D = ⊤
  · have hfin := hI1.2
    rw [HasFiniteIntegral, lintegral_prod _ hI1.1.enorm] at hfin
    simp only [lintegral_const, Measure.restrict_apply_univ, htop] at hfin
    have hK : ∫⁻ y, ‖a y‖ₑ ∂(μ₁.restrict 𝓕₁) = 0 := by
      by_contra hK
      rw [ENNReal.mul_top hK] at hfin
      exact lt_irrefl _ hfin
    have hae : a =ᵐ[μ₁.restrict 𝓕₁] 0 := by
      filter_upwards [(lintegral_eq_zero_iff' hσ.1.enorm).1 hK] with y hy
      simpa using hy
    rw [integral_congr_ae hae]; simp
  · have hr : (ν.restrict D).real univ ≠ 0 := by
      rw [measureReal_def, Measure.restrict_apply_univ]
      exact ENNReal.toReal_ne_zero.2 ⟨hD0, htop⟩
    exact (smul_eq_zero.1 hZ1).resolve_left hr

end GlobalTheory.ProdFundDom
