import Development.WeilBound.ThetaLifts.SmallCones.RightOfCompact
import Development.WeilBound.CoreStatements.ThetaDilations.Nuabs
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain

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

structure Par (μN : Measure N) (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0) : Prop where
  cn : Continuous nn
  ci : Continuous ι
  cm : Continuous mm
  cχ : Continuous χ
  emb : IsClosedEmbedding fun z : N × H × T => nn z.1 * ι z.2.1 * mm z.2.2
  h1 : ∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)
  h2 : ∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u
  h3 : ∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t
  h4 : ∀ u t, mm t * ι u = ι u * mm t
  ne : μN ≠ 0

variable {μN : Measure N} [SigmaFinite μN] [IsFiniteMeasureOnCompacts μN] {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0}
  (ν : Measure G) [ν.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure] (μT : Measure T) [μT.IsHaarMeasure]

theorem haar_eq (h : Par μN nn ι mm χ) {K : Subgroup G} (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]
    (hG : ∀ g, ∃ p u t, ∃ k ∈ K, g = nn p * ι u * mm t * k) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      c * ∫⁻ g, φ g ∂ν = ∫⁻ k, ∫⁻ t, (∫⁻ u, ∫⁻ p, φ (nn p * ι u * mm t * k.1) ∂μN ∂μH) * χ t ∂μT ∂μK := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := right_of_compact μK
  have cn := h.cn.measurable
  have ci := h.ci.measurable
  have cm := h.cm.measurable
  have hχ : Measurable fun s => (χ s : ℝ≥0∞) := h.cχ.measurable.coe_nnreal_ennreal
  set wd := μT.withDensity fun s => (χ s : ℝ≥0∞) with hwd
  haveI : IsLocallyFiniteMeasure wd := IsLocallyFiniteMeasure.withDensity_coe h.cχ
  set ρ := μN.prod (μH.prod wd) with hρ
  have hΨ := h.emb.continuous.measurable
  set l := ρ.map fun z : N × H × T => nn z.1 * ι z.2.1 * mm z.2.2 with hl
  have hmul : Measurable fun z : G × K => z.1 * z.2.1 := by fun_prop
  set m := (l.prod μK).map fun z : G × K => z.1 * z.2.1 with hm
  haveI : IsFiniteMeasureOnCompacts m := ⟨fun C hC => by
    rw [hm, Measure.map_apply hmul hC.measurableSet]
    have hc := hC.mul hK.inv
    refine (measure_mono (t := (C * (K : Set G)⁻¹) ×ˢ univ) fun z hz => ⟨⟨_, hz, z.2.1⁻¹, by simp, by simp⟩, trivial⟩).trans_lt ?_
    rw [Measure.prod_prod, hl, Measure.map_apply hΨ hc.measurableSet]
    exact ENNReal.mul_lt_top (h.emb.isCompact_preimage hc).measure_lt_top (measure_lt_top _ _)⟩
  obtain ⟨c, hc, e⟩ := eq_smul ν m (P := {g | ∃ p u t, g = nn p * ι u * mm t}) (K := K) (by
      rintro _ ⟨p, u, t, rfl⟩
      have := PositivityTheory.PlacePermOperatorBicommutantSpan.nuabs G N H T μN μH μT nn ι mm χ cn ci cm h.cχ.measurable h.h1 h.h2 h.h3 h.h4 p u t
      have e := (MeasurePreserving.prod ⟨measurable_const_mul _, this⟩ (MeasurePreserving.id μK)).map_eq
      rw [hm, Measure.map_map (measurable_const_mul _) hmul]
      conv_rhs => rw [← e, Measure.map_map hmul ((measurable_const_mul _).prodMap measurable_id)]
      exact congrArg (fun f => Measure.map f _) (funext fun z => (mul_assoc _ _ _).symm))
    (fun k hk => by
      have e := (MeasurePreserving.prod (MeasurePreserving.id l) (measurePreserving_mul_right μK ⟨k, hk⟩)).map_eq
      rw [hm, Measure.map_map (measurable_mul_const _) hmul]
      conv_rhs => rw [← e, Measure.map_map hmul (measurable_id.prodMap (measurable_mul_const _))]
      exact congrArg (fun f => Measure.map f _) (funext fun z => mul_assoc _ _ _))
    hK fun g => by
      obtain ⟨p, u, t, k, hk, rfl⟩ := hG g
      exact ⟨_, ⟨p, u, t, rfl⟩, k, hk, rfl⟩
  refine ⟨c, fun h0 => ?_, hc, fun φ hφ => ?_⟩
  · have := congrArg (fun m : Measure G => m univ) e
    simp only [h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at this
    rw [hm, Measure.map_apply hmul MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod, hl,
      Measure.map_apply hΨ MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod, ← univ_prod_univ,
      Measure.prod_prod] at this
    refine mul_ne_zero (mul_ne_zero (Measure.measure_univ_ne_zero.2 h.ne) (mul_ne_zero
      (isOpen_univ.measure_ne_zero μH univ_nonempty) fun h1 => ?_)) (isOpen_univ.measure_ne_zero μK univ_nonempty) this
    rw [hwd, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_eq_zero_iff hχ] at h1
    have := congrFun ((Continuous.ae_eq_iff_eq μT (ENNReal.continuous_coe.comp h.cχ) continuous_zero).1 h1) 1
    simp at this
  · rw [← smul_eq_mul, ← lintegral_smul_measure, ← e, hm, lintegral_map hφ hmul,
      lintegral_prod_symm _ (Measurable.aemeasurable (by fun_prop))]
    refine lintegral_congr fun k => ?_
    rw [hl, lintegral_map (by fun_prop) hΨ, hρ, lintegral_prod_symm _ (Measurable.aemeasurable (by fun_prop)),
      lintegral_prod_symm _ (Measurable.aemeasurable (by fun_prop)), hwd,
      lintegral_withDensity_eq_lintegral_mul _ hχ (by fun_prop)]
    exact lintegral_congr fun t => mul_comm _ _

omit [T2Space G] [LocallyCompactSpace G] in
theorem exists_cut (Q : Subgroup G) [Countable Q] [DiscreteTopology Q] :
    ∃ 𝓖 : Set G, MeasurableSet 𝓖 ∧ (∀ x, ∑' q : Q, 𝓖.indicator (1 : G → ℝ≥0∞) (q.1 * x) = 1) ∧
      ∀ μ : Measure G, IsFundamentalDomain Q 𝓖 μ := by
  obtain ⟨𝓖, h1, h2⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Q
  refine ⟨𝓖, h1, fun x => ?_, fun μ => IsFundamentalDomain.mk' h1.nullMeasurableSet h2⟩
  obtain ⟨q, hq, hu⟩ := h2 x
  exact (tsum_eq_single q fun q' h => indicator_of_notMem (fun h' => h (hu q' h')) _).trans (indicator_of_mem hq _)

theorem fold (h : Par μN nn ι mm χ) {Q ΓN : Subgroup G} [Countable Q] [DiscreteTopology Q] {Γ₁ : Subgroup H} [Countable Γ₁]
    (hN : ΓN ≤ Q) (hNn : ∀ δ ∈ ΓN, ∃ p, δ = nn p) (h₁ : ∀ γ ∈ Γ₁, ι γ ∈ Q)
    (hb : ∀ q ∈ Q, ∃! z : Γ₁ × ΓN, q = ι z.1 * z.2) {C : Set N} (hC : IsCompact C)
    (hcov : ∀ p, ∃ δ ∈ ΓN, ∃ p' ∈ C, δ * nn p = nn p') {D₁ : Set H} (hD₁ : IsFundamentalDomain Γ₁ D₁ μH) :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ⊤ ∧ ∀ β : G → ℝ≥0∞, Measurable β → (∀ x, ∑' q : Q, β (q.1 * x) = 1) →
      ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ p g, φ (nn p * g) = φ g) → (∀ q ∈ Q, ∀ g, φ (q * g) = φ g) → ∀ y,
      ∫⁻ u, ∫⁻ p, β (nn p * ι u * y) * φ (nn p * ι u * y) ∂μN ∂μH = a * ∫⁻ u in D₁, φ (ι u * y) ∂μH := by
  have cn := h.cn.measurable
  have ci := h.ci.measurable
  haveI : Countable ΓN := (Subgroup.inclusion_injective hN).countable
  haveI : DiscreteTopology ΓN := DiscreteTopology.of_continuous_injective
    (continuous_inclusion hN) (Subgroup.inclusion_injective hN)
  obtain ⟨𝓕, f1, -, f3⟩ := exists_cut ΓN
  set l := μN.map nn with hl
  haveI : SMulInvariantMeasure ΓN G l := ⟨fun δ s hs => by
    obtain ⟨p, hp⟩ := hNn δ δ.2
    obtain ⟨L, a1, a2⟩ := h.h1 p
    have e : Measurable fun x : G => δ • x := measurable_const_mul δ.1
    rw [hl, Measure.map_apply cn (e hs), Measure.map_apply cn hs, ← a1.measure_preimage (cn hs).nullMeasurableSet]
    congr 1
    ext x
    simp only [mem_preimage, ← a2, ← hp]
    rfl⟩
  have fd := f3 l
  refine ⟨l 𝓕, fd.measure_ne_zero ?_, ne_top_of_le_ne_top (b := l (nn '' C)) ?_ ?_, fun β hβ hβ1 φ hφ i1 i2 y => ?_⟩
  · rw [hl, Ne, Measure.map_eq_zero_iff cn.aemeasurable]; exact h.ne
  · have hc := hC.image h.cn
    have : IsCompact (nn ⁻¹' (nn '' C)) := by
      have h2 := (h.emb.isCompact_preimage hc).image continuous_fst
      refine h2.of_isClosed_subset (hc.isClosed.preimage h.cn) fun p hp => ⟨(p, 1, 1), by simpa using hp, rfl⟩
    rw [hl, Measure.map_apply cn hc.measurableSet]
    exact this.measure_lt_top.ne
  · have hm := (hC.image h.cn).measurableSet
    rw [fd.measure_eq_tsum' (nn '' C)]
    have hS : MeasurableSet (⋃ δ : ΓN, δ • (nn '' C)) := MeasurableSet.iUnion fun δ => hm.const_smul δ
    have e : l 𝓕 = l (𝓕 ∩ ⋃ δ : ΓN, δ • (nn '' C)) := by
      rw [hl, Measure.map_apply cn f1, Measure.map_apply cn (f1.inter hS)]
      congr 1
      ext p
      refine ⟨fun hp => ⟨hp, ?_⟩, fun hp => hp.1⟩
      obtain ⟨δ, h1, p', h2, h3⟩ := hcov p
      exact mem_iUnion.2 ⟨⟨δ, h1⟩⁻¹, mem_smul_set_iff_inv_smul_mem.2 ⟨p', h2, by simpa using h3.symm⟩⟩
    rw [e, inter_iUnion]
    refine (measure_iUnion_le _).trans (le_of_eq ?_)
    rw [← (Equiv.inv ΓN).tsum_eq]
    refine tsum_congr fun δ => ?_
    rw [← measure_smul l δ, smul_set_inter, Equiv.inv_apply, smul_inv_smul, inter_comm]
  · let e : Γ₁ × ΓN ≃ Q := Equiv.ofBijective (fun z => ⟨ι z.1 * z.2, Q.mul_mem (h₁ _ z.1.2) (hN z.2.2)⟩)
      ⟨fun z z' hz => (hb _ (Q.mul_mem (h₁ _ z.1.2) (hN z.2.2))).unique rfl (congrArg Subtype.val hz), fun q => by
        obtain ⟨z, hz, -⟩ := hb q q.2
        exact ⟨z, Subtype.ext hz.symm⟩⟩
    have inner : ∀ x, ∑' γ : Γ₁, ∫⁻ p, β (nn p * ι γ * x) ∂μN = l 𝓕 := fun x => by
      have e1 : ∀ γ : Γ₁, ∫⁻ p, β (nn p * ι γ * x) ∂μN = ∑' δ : ΓN, ∫⁻ g in 𝓕, β (ι γ * δ * (g * x)) ∂l := fun γ => by
        obtain ⟨L, a1, a2⟩ := h.h2 γ
        rw [← a1.lintegral_comp (f := fun p => β (nn p * ι γ * x)) (by fun_prop)]
        simp only [← a2]
        rw [← lintegral_map (f := fun g => β (ι γ * g * x)) (by fun_prop) cn, ← hl, fd.lintegral_eq_tsum'']
        simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
      simp only [e1]
      rw [← ENNReal.tsum_prod, ← lintegral_tsum fun z => Measurable.aemeasurable (by fun_prop)]
      have : ∀ g, ∑' z : Γ₁ × ΓN, β (ι z.1 * z.2 * (g * x)) = 1 := fun g => by
        rw [← hβ1 (g * x), ← e.tsum_eq]; rfl
      simp only [this, lintegral_one, Measure.restrict_apply_univ]
    have e2 : ∀ u, ∫⁻ p, β (nn p * ι u * y) * φ (nn p * ι u * y) ∂μN = (∫⁻ p, β (nn p * ι u * y) ∂μN) * φ (ι u * y) :=
      fun u => by
        simp only [mul_assoc _ (ι u), i1]
        rw [lintegral_mul_const _ (by fun_prop)]
    simp only [e2]
    rw [hD₁.lintegral_eq_tsum'', ← lintegral_tsum fun γ => Measurable.aemeasurable (by fun_prop),
      ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr fun u => ?_
    simp only [Subgroup.smul_def, smul_eq_mul, map_mul, mul_assoc, i2 _ (h₁ _ (Subtype.prop _))]
    rw [ENNReal.tsum_mul_right, ← inner (ι u * y)]
    simp only [mul_assoc]

end PositivityTheory.ThKCT.Unf
