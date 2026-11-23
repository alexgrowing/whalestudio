import Mathlib
open MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace GlobalTheory

theorem bruhat_weight_exists : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (P K : Subgroup G) (μP : Measure P),
    IsClosed (P : Set G) → IsCompact (K : Set G) → μP.IsHaarMeasure → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g : G, (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ 0 ∧ (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ ∞ := by
  intro G _ _ _ _ _ _ _ _ P K μP hP hK hμ hPK
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hCc : IsCompact (V * (K : Set G)) := hVc.mul hK
  have hCm : MeasurableSet (V * (K : Set G)) := hCc.isClosed.measurableSet
  refine ⟨(V * (K : Set G)).indicator 1, measurable_one.indicator hCm, fun g => ?_⟩
  have hf : Topology.IsClosedEmbedding (fun q : P => (q : G) * g) :=
    (Homeomorph.mulRight g).isClosedEmbedding.comp hP.isClosedEmbedding_subtypeVal
  have hSc : IsCompact ((fun q : P => (q : G) * g) ⁻¹' (V * (K : Set G))) := hf.isCompact_preimage hCc
  have hSm : MeasurableSet ((fun q : P => (q : G) * g) ⁻¹' (V * (K : Set G))) :=
    hCm.preimage hf.continuous.measurable
  have heq : (∫⁻ q : P, (V * (K : Set G)).indicator 1 ((q : G) * g) ∂μP)
      = μP ((fun q : P => (q : G) * g) ⁻¹' (V * (K : Set G))) := by
    rw [← lintegral_indicator_one hSm]
    rfl
  rw [heq]
  refine ⟨?_, hSc.measure_lt_top.ne⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
  have hUo : IsOpen ((fun q : P => (q : G) * p) ⁻¹' interior V) :=
    isOpen_interior.preimage (by fun_prop)
  have hUne : ((fun q : P => (q : G) * p) ⁻¹' interior V).Nonempty :=
    ⟨⟨p⁻¹, P.inv_mem hp⟩, by simpa using mem_interior_iff_mem_nhds.mpr hV1⟩
  have hUS : (fun q : P => (q : G) * p) ⁻¹' interior V
      ⊆ (fun q : P => (q : G) * (p * k)) ⁻¹' (V * (K : Set G)) := by
    intro q hq
    show (q : G) * (p * k) ∈ V * (K : Set G)
    rw [← mul_assoc]
    exact Set.mul_mem_mul (interior_subset hq) hk
  exact ((hUo.measure_pos μP hUne).trans_le (measure_mono hUS)).ne'

end GlobalTheory
