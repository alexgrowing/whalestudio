import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrou
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.SnMass.ProdQuot

theorem isHaarMeasure_of_sigmaFinite {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] (ν : Measure H)
    [SigmaFinite ν] [ν.IsMulLeftInvariant] (hν : ν ≠ 0) : ν.IsHaarMeasure := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have e := Measure.haarMeasure_unique ν K
  rw [e]
  refine Measure.IsHaarMeasure.smul _ (fun hc => hν (by rw [e, hc, zero_smul])) fun hc => hν ?_
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top ν n
  have h2 : ν (spanningSets ν n) = ⊤ * Measure.haarMeasure K (spanningSets ν n) := by
    have := congrArg (fun ρ : Measure H => ρ (spanningSets ν n)) e
    simpa [hc] using this
  by_cases h3 : Measure.haarMeasure K (spanningSets ν n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

theorem exists_cutoff {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (R : Subgroup G) (μ : Measure G)
    [SigmaFinite μ] (hR : IsClosed (R : Set G)) (h0 : μ ≠ 0) (hc : μ (R : Set G)ᶜ = 0)
    (hi : ∀ s ∈ R, μ.map (fun x => s * x) = μ ∧ μ.map (fun x => x * s) = μ) :
    ∃ b : G → ℝ≥0, Measurable b ∧ ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1 := by
  have hce : Topology.IsClosedEmbedding R.subtype := hR.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding R.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap R.subtype).map R.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range R.subtype = (R : Set G) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure R := μ.comap R.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => (g : G) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← (hi g g.2).1, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsMulRightInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => x * (g : G) := measurable_mul_const _
    rw [Measure.map_map hφ.measurable (measurable_mul_const g), h2]
    conv_rhs => rw [← (hi g g.2).2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure := isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  obtain ⟨b, hb, h1⟩ := GlobalTheory.exists_measurable_lintegral_coset_eq_one G R ν R.subtype hce
  refine ⟨fun x => (b x).toNNReal, hb.ennreal_toNNReal, fun g => ?_⟩
  have hm : Measurable fun s => b (s * g) := hb.comp (measurable_mul_const g)
  have h3 : ∫⁻ s, b (s * g) ∂μ = 1 := by
    rw [← h2, hφ.lintegral_map]
    exact h1 g
  rw [← h3]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lt_top hm (by rw [h3]; exact ENNReal.one_ne_top)] with s hs
  exact ENNReal.coe_toNNReal hs.ne

theorem map_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ν.map F = (μG.withDensity fun x => b x).map F := by
  have hb' : Measurable fun x => (b x : ℝ≥0∞) := hb.coe_nnreal_ennreal
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), hν _ (hb'.indicator (hF hA)), ← lintegral_indicator_one (hF hA)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ F ⁻¹' A
  · rw [Set.indicator_of_mem hx, Pi.one_apply, ← h1 x]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_mem (by simpa [hs] using hx)]
  · rw [Set.indicator_of_notMem hx, ← lintegral_zero (μ := μ)]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_notMem (by simpa [hs] using hx)]

theorem integral_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ∫ x, F x ∂ν = ∫ x, (b x : ℂ) * F x ∂μG ∧ (Integrable F ν ↔ Integrable (fun x => (b x : ℂ) * F x) μG) := by
  have h := map_eq μG μ ν hb h1 hν hF hi
  have e : (fun x => (b x : ℂ) * F x) = fun x => b x • F x := by
    ext x
    simp [NNReal.smul_def]
  have hid : ∀ ρ : Measure ℂ, AEStronglyMeasurable (fun z : ℂ => z) ρ := fun ρ => continuous_id.aestronglyMeasurable
  rw [e]
  constructor
  · rw [← integral_withDensity_eq_integral_smul hb, ← integral_map hF.aemeasurable (hid _),
      ← integral_map hF.aemeasurable (hid _), h]
  · rw [← integrable_withDensity_iff_integrable_smul hb]
    have h2 := integrable_map_measure (μ := ν) (hid _) hF.aemeasurable
    have h3 := integrable_map_measure (μ := μG.withDensity fun x => b x) (hid _) hF.aemeasurable
    rw [h] at h2
    exact h2.symm.trans h3

end GlobalTheory.SnMass.ProdQuot
