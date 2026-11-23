import Development.WeilBound.ThetaLifts.SmallCones.UnfAbs

open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise

namespace PositivityTheory.ThKCT.Unf

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {T : Type} [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  {μN : Measure N} [SigmaFinite μN] [IsFiniteMeasureOnCompacts μN] {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0}
  (ν : Measure G) [ν.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure] (μT : Measure T) [μT.IsHaarMeasure]

theorem integral_eq_of {X : Type} [MeasurableSpace X] {μ₁ μ₂ : Measure X} {f : X → ℂ} (hf : Measurable f)
    (h : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → ∫⁻ x, ψ (f x) ∂μ₁ = ∫⁻ x, ψ (f x) ∂μ₂) : ∫ x, f x ∂μ₁ = ∫ x, f x ∂μ₂ := by
  have e : μ₁.map f = μ₂.map f := by
    ext s hs
    rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) hf,
      lintegral_map (measurable_one.indicator hs) hf, h _ (measurable_one.indicator hs)]
  have k : ∀ μ : Measure X, ∫ x, f x ∂μ = ∫ z, z ∂(μ.map f) := fun μ =>
    (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
  rw [k, k, e]

theorem unfold_abs (h : Par μN nn ι mm χ) {K : Subgroup G} (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]
    (hG : ∀ g, ∃ p u t, ∃ k ∈ K, g = nn p * ι u * mm t * k) {Γ Q ΓN : Subgroup G} [Countable Γ] [DiscreteTopology Γ]
    (hQ : Q ≤ Γ) {Γ₁ : Subgroup H} [Countable Γ₁]
    (hN : ΓN ≤ Q) (hNn : ∀ δ ∈ ΓN, ∃ p, δ = nn p) (h₁ : ∀ γ ∈ Γ₁, ι γ ∈ Q)
    (hb : ∀ q ∈ Q, ∃! z : Γ₁ × ΓN, q = ι z.1 * z.2) {C : Set N} (hC : IsCompact C)
    (hcov : ∀ p, ∃ δ ∈ ΓN, ∃ p' ∈ C, δ * nn p = nn p') {D₁ : Set H} (hD₁ : IsFundamentalDomain Γ₁ D₁ μH)
    {D : Set G} (hD : IsFundamentalDomain Γ D ν) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (I : Type) (r : I → G), (∀ x, r x ∈ Γ) → (∀ γ ∈ Γ, ∃! x, γ * (r x)⁻¹ ∈ Q) → ∀ f : G → ℂ, Continuous f →
      (∀ p g, f (nn p * g) = f g) → (∀ q ∈ Q, ∀ g, f (q * g) = f g) →
      ∫⁻ k, ∫⁻ t, (∫⁻ u in D₁, ‖f (ι u * mm t * k.1)‖ₑ ∂μH) * χ t ∂μT ∂μK < ⊤ →
      (∀ᵐ g ∂(ν.restrict D), Summable fun x => f (r x * g)) ∧ IntegrableOn (fun g => ∑' x, f (r x * g)) D ν ∧
        ∫ g in D, ∑' x, f (r x * g) ∂ν = κ * ∫ k, ∫ t, (∫ u in D₁, f (ι u * mm t * k.1) ∂μH) * ((χ t : ℝ) : ℂ) ∂μT ∂μK := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Countable Q := (Subgroup.inclusion_injective hQ).countable
  haveI : DiscreteTopology Q := DiscreteTopology.of_continuous_injective
    (continuous_inclusion hQ) (Subgroup.inclusion_injective hQ)
  have ci := h.ci.measurable
  have cm := h.cm.measurable
  have hχ : Measurable fun s => (χ s : ℝ≥0∞) := h.cχ.measurable.coe_nnreal_ennreal
  obtain ⟨c, c0, c1, hc⟩ := haar_eq ν μH μT h hK μK hG
  obtain ⟨a, a0, a1, ha⟩ := fold μH h hN hNn h₁ hb hC hcov hD₁
  obtain ⟨𝓖, g1, g2, g3⟩ := exists_cut Q
  have k0 : a / c ≠ 0 := (ENNReal.div_pos a0 c1).ne'
  have k1 : a / c ≠ ⊤ := ENNReal.div_ne_top a1 c0
  refine ⟨(a / c).toReal, ENNReal.toReal_pos k0 k1, fun I r hr hu f hf i1 i2 hfin => ?_⟩
  have hinj : Function.Injective fun x => (⟨r x, hr x⟩ : Γ) := fun x x' e =>
    (hu _ (hr x)).unique (by simp) (by rw [show r x = r x' from congrArg Subtype.val e]; simp)
  haveI := hinj.countable
  obtain ⟨𝓕, f1, f2⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.unf G ν Γ Q hQ D hD I r hr hu
  have key : ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ p g, φ (nn p * g) = φ g) → (∀ q ∈ Q, ∀ g, φ (q * g) = φ g) →
      ∫⁻ g in D, ∑' x, φ (r x * g) ∂ν = a / c * ∫⁻ k, ∫⁻ t, (∫⁻ u in D₁, φ (ι u * mm t * k.1) ∂μH) * χ t ∂μT ∂μK :=
    fun φ hφ j1 j2 => by
      have hβ : Measurable (𝓖.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator g1
      have e1 : ∫⁻ g in 𝓖, φ g ∂ν = ∫⁻ g, 𝓖.indicator 1 g * φ g ∂ν := by
        rw [← lintegral_indicator g1]
        exact lintegral_congr fun g => by by_cases h : g ∈ 𝓖 <;> simp [h]
      have e2 := hc (fun g => 𝓖.indicator 1 g * φ g) (hβ.mul hφ)
      simp only [mul_assoc _ (mm _), ha _ hβ g2 φ hφ j1 j2, mul_assoc a] at e2
      simp only [lintegral_const_mul' _ _ a1] at e2
      rw [f2 φ hφ, f1.setLIntegral_eq (g3 ν) φ fun q x => j2 q q.2 x, e1, ENNReal.div_eq_inv_mul, mul_assoc]
      simp only [mul_assoc _ (mm _)]
      rw [← e2, ← mul_assoc, ENNReal.inv_mul_cancel c0 c1, one_mul]
  have hm := hf.measurable
  have n1 := key (fun g => ‖f g‖ₑ) hm.enorm (fun p g => by rw [i1]) fun q hq g => by rw [i2 q hq]
  have n2 : ∫⁻ g in D, ∑' x, ‖f (r x * g)‖ₑ ∂ν < ⊤ := by rw [n1]; exact ENNReal.mul_lt_top k1.lt_top hfin
  have hx : ∀ x, Measurable fun g => f (r x * g) := fun x => hm.comp (measurable_const_mul _)
  refine ⟨(ae_lt_top (Measurable.tsum fun x => (hx x).enorm) n2.ne).mono fun g hg => ?_,
    ⟨(Measurable.tsum hx).aestronglyMeasurable, (lintegral_mono fun g => enorm_tsum_le_tsum_enorm).trans_lt n2⟩, ?_⟩
  · exact Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 hg.ne)
  set wd := μT.withDensity fun s => (χ s : ℝ≥0∞) with hwd
  set ρ := μK.prod (wd.prod (μH.restrict D₁)) with hρ
  have hπ : Measurable fun z : K × T × H => ι z.2.2 * mm z.2.1 * z.1.1 := by fun_prop
  have L1 : ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ g, φ g ∂(Measure.sum fun x => (ν.restrict D).map (r x * ·)) =
      ∫⁻ g in D, ∑' x, φ (r x * g) ∂ν := fun φ hφ => by
    rw [lintegral_sum_measure, lintegral_tsum fun x => Measurable.aemeasurable (by fun_prop)]
    exact tsum_congr fun x => lintegral_map hφ (measurable_const_mul _)
  have L2 : ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ z, φ (ι z.2.2 * mm z.2.1 * z.1.1) ∂ρ =
      ∫⁻ k, ∫⁻ t, (∫⁻ u in D₁, φ (ι u * mm t * k.1) ∂μH) * χ t ∂μT ∂μK := fun φ hφ => by
    rw [hρ, lintegral_prod _ (Measurable.aemeasurable (by fun_prop))]
    refine lintegral_congr fun k => ?_
    rw [lintegral_prod _ (Measurable.aemeasurable (by fun_prop)), hwd,
      lintegral_withDensity_eq_lintegral_mul _ hχ (by fun_prop)]
    exact lintegral_congr fun t => mul_comm _ _
  have I1 : Integrable f (Measure.sum fun x => (ν.restrict D).map (r x * ·)) :=
    ⟨hm.aestronglyMeasurable, (L1 _ hm.enorm).trans_lt n2⟩
  have I2 : Integrable (fun z : K × T × H => f (ι z.2.2 * mm z.2.1 * z.1.1)) ρ :=
    ⟨(hm.comp hπ).aestronglyMeasurable, (L2 _ hm.enorm).trans_lt hfin⟩
  have e := integral_eq_of (μ₁ := Measure.sum fun x => (ν.restrict D).map (r x * ·))
    (μ₂ := (a / c) • ρ.map fun z : K × T × H => ι z.2.2 * mm z.2.1 * z.1.1) hm fun ψ hψ => by
      rw [L1 (fun g => ψ (f g)) (hψ.comp hm), lintegral_smul_measure, lintegral_map (f := fun g => ψ (f g)) (hψ.comp hm) hπ,
        smul_eq_mul]
      exact (key (fun g => ψ (f g)) (hψ.comp hm) (fun p g => congrArg ψ (i1 p g)) fun q hq g => congrArg ψ (i2 q hq g)).trans
        (congrArg _ (L2 (fun g => ψ (f g)) (hψ.comp hm)).symm)
  rw [integral_sum_measure I1, integral_smul_measure, integral_map hπ.aemeasurable hm.aestronglyMeasurable, hρ,
    integral_prod _ I2] at e
  rw [integral_tsum (fun x => (hx x).aestronglyMeasurable)
    (by rw [← lintegral_tsum fun x => (hx x).enorm.aemeasurable]; exact n2.ne)]
  refine Eq.trans (tsum_congr fun x => (integral_map (measurable_const_mul _).aemeasurable hm.aestronglyMeasurable).symm)
    (e.trans ?_)
  rw [Complex.real_smul]
  congr 1
  refine integral_congr_ae (I2.prod_right_ae.mono fun k hk => ?_)
  simp only at hk ⊢
  rw [integral_prod _ hk, hwd, integral_withDensity_eq_integral_smul h.cχ.measurable]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [NNReal.smul_def, Complex.real_smul, mul_comm]

end PositivityTheory.ThKCT.Unf
