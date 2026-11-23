import Mathlib

open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.Pf.Weil

namespace QuotInt

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] {H : Subgroup G}

lemma measurable_mulH : Measurable (fun p : G × H => p.1 * (p.2 : G)) := by
  exact measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)

noncomputable def fib (κ : Measure H) (f : G → ℝ≥0∞) (g : G) : ℝ≥0∞ := ∫⁻ h, f (g * h) ∂κ

lemma measurable_fib (κ : Measure H) [SFinite κ] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fib κ f) := by
  exact (hf.comp measurable_mulH).lintegral_prod_right'

lemma fib_mul (κ : Measure H) [κ.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (h₀ : H) :
    fib κ f (g * h₀) = fib κ f g := by
  unfold fib
  have key := lintegral_mul_left_eq_self (μ := κ) (fun h : H => f (g * (h : G))) h₀
  simpa [mul_assoc] using key

lemma measurable_mk : Measurable ((↑) : G → G ⧸ H) := by
  first | exact measurable_quotient_mk'' | exact measurable_quotient_mk' | exact fun s hs => hs

lemma measure_coset_le (κ : Measure H) [κ.IsMulLeftInvariant] (y : G) (E : Set G) :
    κ {h : H | y * h ∈ E} ≤ κ {h : H | (h : G) ∈ E⁻¹ * E} := by
  by_cases hne : ∃ h₀ : H, y * (h₀ : G) ∈ E
  · obtain ⟨h₀, hh₀⟩ := hne
    calc κ {h : H | y * h ∈ E}
        ≤ κ ((fun h : H => h₀⁻¹ * h) ⁻¹' {h : H | (h : G) ∈ E⁻¹ * E}) := by
          apply measure_mono
          intro h hh
          have hh' : y * (h : G) ∈ E := hh
          show ((h₀⁻¹ * h : H) : G) ∈ E⁻¹ * E
          rw [Set.mem_mul]
          refine ⟨(y * h₀)⁻¹, by rw [Set.mem_inv, inv_inv]; exact hh₀, y * h, hh', ?_⟩
          push_cast
          group
      _ = κ {h : H | (h : G) ∈ E⁻¹ * E} := measure_preimage_mul κ _ _
  · push_neg at hne
    have h0 : κ {h : H | y * h ∈ E} = 0 :=
      measure_mono_null (fun h hh => (hne h hh).elim) measure_empty
    rw [h0]
    first | exact zero_le _ | exact zero_le | simp

lemma measure_coset_lt_top (hH : IsClosed (H : Set G)) (κ : Measure H)
    [IsFiniteMeasureOnCompacts κ] {E : Set G} (hE : IsCompact E) :
    κ {h : H | (h : G) ∈ E⁻¹ * E} < ∞ := by
  have hc : IsCompact (E⁻¹ * E) := hE.inv.mul hE
  have hc2 : IsCompact {h : H | (h : G) ∈ E⁻¹ * E} := by
    first
    | exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hc
    | exact hH.closedEmbedding_subtype_val.isCompact_preimage hc
    | (rw [Subtype.isCompact_iff]
       have e : ((↑) : H → G) '' {h : H | (h : G) ∈ E⁻¹ * E} = (E⁻¹ * E) ∩ (H : Set G) := by
         ext x
         simp
       rw [e]
       exact hc.inter_right hH)
  exact hc2.measure_lt_top

lemma measure_nhds_pos (κ : Measure H) [IsOpenPosMeasure κ] {V : Set G} (hV : V ∈ 𝓝 (1 : G)) :
    0 < κ {h : H | (h : G) ∈ V} := by
  have h1 : ((↑) : H → G) ⁻¹' V ∈ 𝓝 (1 : H) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hV
  first
  | exact measure_pos_of_mem_nhds κ h1
  | exact (measure_pos_of_nonempty_interior κ ⟨1, mem_interior_iff_mem_nhds.2 h1⟩)

lemma exists_fib_eq_one (hH : IsClosed (H : Set G)) (κ : Measure H) [SFinite κ]
    [κ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts κ] [IsOpenPosMeasure κ] :
    ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ x, fib κ β x = 1 := by
  obtain ⟨φ, hφ, hpos, hfin⟩ : ∃ φ : G → ℝ≥0∞, Measurable φ ∧ (∀ x, 0 < fib κ φ x) ∧
      (∀ x, fib κ φ x < ∞) := by
    obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
    have hVm : MeasurableSet V := hVc.isClosed.measurableSet
    let d := TopologicalSpace.denseSeq G
    have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq G
    have hS : ∀ y : G, MeasurableSet {h : H | y * (h : G) ∈ V} := fun y =>
      hVm.preimage ((measurable_const_mul y).comp measurable_subtype_coe)
    have hfib : ∀ x, fib κ (fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * V.indicator 1 ((d n)⁻¹ * x)) x
        = ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V} := by
      intro x
      have hm1 : ∀ n, Measurable (fun h : H => V.indicator (1 : G → ℝ≥0∞) ((d n)⁻¹ * (x * (h : G)))) :=
        fun n => (measurable_one.indicator hVm).comp
          ((measurable_const_mul _).comp ((measurable_const_mul x).comp measurable_subtype_coe))
      have hm : ∀ n, Measurable (fun h : H =>
          (2⁻¹ : ℝ≥0∞) ^ n * V.indicator (1 : G → ℝ≥0∞) ((d n)⁻¹ * (x * (h : G)))) :=
        fun n => measurable_const.mul (hm1 n)
      show ∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * V.indicator (1 : G → ℝ≥0∞) ((d n)⁻¹ * (x * (h : G))) ∂κ = _
      rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
      congr 1
      funext n
      rw [lintegral_const_mul _ (hm1 n)]
      congr 1
      rw [← lintegral_indicator_one (hS ((d n)⁻¹ * x))]
      congr 1
      funext h
      simp only [Function.comp_apply, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, mul_assoc]
      first | rfl | simp [Set.indicator_apply]
    have hC : κ {h : H | (h : G) ∈ V⁻¹ * V} < ∞ := measure_coset_lt_top hH κ hVc
    refine ⟨fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * V.indicator 1 ((d n)⁻¹ * x), ?_, ?_, ?_⟩
    · exact Measurable.ennreal_tsum (fun n => measurable_const.mul
        ((measurable_one.indicator hVm).comp (measurable_const_mul _)))
    · intro x
      rw [hfib x]
      have hopen : IsOpen {g : G | g⁻¹ * x ∈ interior V} :=
        isOpen_interior.preimage (continuous_inv.mul continuous_const)
      obtain ⟨n, hn⟩ := hd.exists_mem_open hopen ⟨x, by simpa using mem_interior_iff_mem_nhds.2 hV1⟩
      have hn' : (d n)⁻¹ * x ∈ interior V := hn
      have hnb : {z : G | (d n)⁻¹ * x * z ∈ V} ∈ 𝓝 (1 : G) := by
        have hc : ContinuousAt (fun z : G => (d n)⁻¹ * x * z) 1 :=
          (continuous_const.mul continuous_id).continuousAt
        have hV' : V ∈ 𝓝 ((fun z : G => (d n)⁻¹ * x * z) 1) := by
          simpa using mem_interior_iff_mem_nhds.1 hn'
        exact hc.preimage_mem_nhds hV'
      have hpos' := measure_nhds_pos κ hnb
      calc (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V} :=
            ENNReal.mul_pos (by simp) hpos'.ne'
        _ ≤ _ := ENNReal.le_tsum n
    · intro x
      rw [hfib x]
      have hle : ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V}
          ≤ ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (h : G) ∈ V⁻¹ * V} := by
        have hn : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (d n)⁻¹ * x * (h : G) ∈ V}
            ≤ (2⁻¹ : ℝ≥0∞) ^ n * κ {h : H | (h : G) ∈ V⁻¹ * V} := by
          intro n
          first
          | exact mul_le_mul_of_nonneg_left (measure_coset_le κ _ V) (by simp)
          | exact mul_le_mul_left (measure_coset_le κ _ V) _
        first
        | exact ENNReal.tsum_le_tsum hn
        | exact tsum_le_tsum hn ENNReal.summable ENNReal.summable
        | exact Summable.tsum_le_tsum hn ENNReal.summable ENNReal.summable
      refine lt_of_le_of_lt hle ?_
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      first
      | exact ENNReal.mul_lt_top (by simp) hC
      | exact ENNReal.mul_lt_top (by simp) hC.ne
  refine ⟨fun x => φ x * (fib κ φ x)⁻¹, ?_, ?_⟩
  · first
    | exact hφ.mul (measurable_fib κ hφ).inv
    | exact hφ.mul (ENNReal.continuous_inv.measurable.comp (measurable_fib κ hφ))
  · intro x
    have e : ∀ h : H, φ (x * h) * (fib κ φ (x * h))⁻¹ = φ (x * h) * (fib κ φ x)⁻¹ := fun h => by
      rw [fib_mul]
    show ∫⁻ h, φ (x * h) * (fib κ φ (x * h))⁻¹ ∂κ = 1
    simp_rw [e]
    have hφx : Measurable (fun h : H => φ (x * (h : G))) :=
      hφ.comp ((measurable_const_mul x).comp measurable_subtype_coe)
    rw [lintegral_mul_const _ hφx]
    exact ENNReal.mul_inv_cancel (hpos x).ne' (hfin x).ne

section Main

variable (μ : Measure G) (ν : Measure H)

noncomputable def qmeas (H : Subgroup G) (μ : Measure G) (β : G → ℝ≥0∞) : Measure (G ⧸ H) :=
  (μ.withDensity β).map ((↑) : G → G ⧸ H)

variable [SFinite μ] [μ.IsMulRightInvariant] [SFinite ν] [ν.IsMulLeftInvariant]
  {β : G → ℝ≥0∞} (hβ : Measurable β) (hβ1 : ∀ x, ∫⁻ h, β (x * (h : G)⁻¹) ∂ν = 1)
include hβ hβ1

end Main

end QuotInt

end Formalism.L2.SG.Pf.Weil
