import Mathlib

open MeasureTheory Pointwise

namespace GlobalTheory

theorem ae_ae_subgroup_mul_of_ae {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H)
    [SFinite ν] {P : G → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ g ∂μ, ∀ᵐ p : H ∂ν, P ((p : G) * g) := by
  have hΦ : MeasurePreserving (fun z : H × G => (id z.1, (z.1 : G) * z.2))
      (ν.prod μ) (ν.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun (p : H) (x : G) => (p : G) * x)
      (MeasurePreserving.id ν) ?_ ?_
    · exact (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
    · exact Filter.Eventually.of_forall fun p => map_mul_left_eq_self μ (p : G)
  have h1 : ∀ᵐ z ∂(ν.prod μ), P z.2 := by
    rw [ae_iff]
    have : {z : H × G | ¬ P z.2} = Set.univ ×ˢ {x | ¬ P x} := by ext z; simp
    rw [this, Measure.prod_prod, (ae_iff).1 hP, mul_zero]
  have h2 : ∀ᵐ z ∂(ν.prod μ), P ((z.1 : G) * z.2) := hΦ.quasiMeasurePreserving.ae h1
  have h3 : ∀ᵐ w ∂(μ.prod ν), P ((w.2 : G) * w.1) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae h2
  exact Measure.ae_ae_of_ae_prod h3

theorem ae_measure_subgroup_slice_fundamentalDomain {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (H : Subgroup G) (ν : Measure H) [SFinite ν] (Γ : Subgroup G) [Countable Γ]
    (hΓH : Γ ≤ H) (hinv : ∀ γ ∈ Γ.subgroupOf H, MeasurePreserving (fun p : H => γ * p) ν ν)
    (𝓓 : Set G) (h𝓓 : IsFundamentalDomain Γ 𝓓 μ) (E : Set H)
    (hE : IsFundamentalDomain (Γ.subgroupOf H) E ν) :
    ∀ᵐ g ∂μ, ν {p : H | (p : G) * g ∈ 𝓓} = ν E := by
  classical
  haveI : Countable (Γ.subgroupOf H) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf H =>
      (⟨((x : H) : G), Subgroup.mem_subgroupOf.1 x.2⟩ : Γ)) ?_
    intro x y hxy
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val hxy
  haveI : MeasurableConstSMul (Γ.subgroupOf H) H :=
    ⟨fun c => (measurable_subtype_coe.const_mul ((c : H) : G)).subtype_mk⟩
  haveI : SMulInvariantMeasure (Γ.subgroupOf H) H ν :=
    ⟨fun c s hs => (hinv c c.2).measure_preimage hs.nullMeasurableSet⟩
  obtain ⟨t, hts, ht, htD⟩ := h𝓓.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hcov := ae_ae_subgroup_mul_of_ae μ H ν h𝓓.ae_covers
  have hdisj0 : ∀ᵐ x ∂μ, ∀ γ δ : Γ, γ ≠ δ → ¬ (x ∈ γ • 𝓓 ∧ x ∈ δ • 𝓓) := by
    rw [ae_all_iff]; intro γ; rw [ae_all_iff]; intro δ
    by_cases hγδ : γ = δ
    · exact Filter.Eventually.of_forall fun x h => absurd hγδ h
    · have := h𝓓.aedisjoint hγδ
      have h0 : μ ((γ • 𝓓) ∩ (δ • 𝓓)) = 0 := this
      rw [measure_eq_zero_iff_ae_notMem] at h0
      exact h0.mono fun x hx _ hm => hx hm
  have hdisj := ae_ae_subgroup_mul_of_ae μ H ν hdisj0
  have hmeas := ae_ae_subgroup_mul_of_ae μ H ν (htD.mem_iff)
  filter_upwards [hcov, hdisj, hmeas] with g h1 h2 h3
  have hA : IsFundamentalDomain (Γ.subgroupOf H) {p : H | (p : G) * g ∈ 𝓓} ν := by
    refine ⟨?_, ?_, ?_⟩
    · have hA' : MeasurableSet {p : H | (p : G) * g ∈ t} :=
        (measurable_subtype_coe.mul_const g) ht
      refine hA'.nullMeasurableSet.congr ?_
      exact h3.mono fun p hp => propext hp
    · refine h1.mono fun p hp => ?_
      obtain ⟨γ, hγ⟩ := hp
      refine ⟨⟨⟨(γ : G), hΓH γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_⟩
      show (((γ : G) * p) * g) ∈ 𝓓
      rw [mul_assoc]; exact hγ
    · intro γ δ hγδ
      show ν ((γ • {p : H | (p : G) * g ∈ 𝓓}) ∩ (δ • {p : H | (p : G) * g ∈ 𝓓})) = 0
      rw [measure_eq_zero_iff_ae_notMem]
      refine h2.mono fun q hq hm => ?_
      have hne : (⟨((γ : H) : G), Subgroup.mem_subgroupOf.1 γ.2⟩ : Γ) ≠
          ⟨((δ : H) : G), Subgroup.mem_subgroupOf.1 δ.2⟩ := by
        intro h; apply hγδ; apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val h
      apply hq _ _ hne
      obtain ⟨h1', h2'⟩ := hm
      rw [Set.mem_smul_set_iff_inv_smul_mem] at h1' h2'
      rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
      refine ⟨?_, ?_⟩
      · have : ((((γ⁻¹ • q : H)) : G) * g) ∈ 𝓓 := h1'
        show ((γ : H) : G)⁻¹ * ((q : G) * g) ∈ 𝓓
        rw [← mul_assoc]; simpa [Subgroup.smul_def] using this
      · have : ((((δ⁻¹ • q : H)) : G) * g) ∈ 𝓓 := h2'
        show ((δ : H) : G)⁻¹ * ((q : G) * g) ∈ 𝓓
        rw [← mul_assoc]; simpa [Subgroup.smul_def] using this
  exact hA.measure_eq hE

end GlobalTheory
