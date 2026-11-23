import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf

section Abs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem map_comap_subgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G)
    (hc : μ (H : Set G)ᶜ = 0) : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ := by
  have he : MeasurableEmbedding ((↑) : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  rw [he.map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine le_antisymm (le_trans (measure_mono ?_) hc.le) zero_le
  intro x hx h
  exact hx ⟨⟨x, h⟩, rfl⟩

theorem haarOnSet_isHaar (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G) (hσ : SigmaFinite μ)
    (h0 : μ ≠ 0) (hc : μ (H : Set G)ᶜ = 0) (hinv : ∀ s ∈ H, μ.map (fun x => s * x) = μ) :
    (μ.comap ((↑) : H → G)).IsHaarMeasure ∧ (∀ K : Set G, IsCompact K → μ K < ⊤) ∧
      ∀ U : Set G, IsOpen U → (U ∩ (H : Set G)).Nonempty → 0 < μ U := by
  have he : MeasurableEmbedding ((↑) : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  have hmap : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ := map_comap_subgroup H hH μ hc
  have hce : Topology.IsClosedEmbedding ((↑) : H → G) := by
    first
      | exact hH.isClosedEmbedding_subtypeVal
      | exact hH.closedEmbedding_subtype_val
  haveI : LocallyCompactSpace H := hce.locallyCompactSpace
  haveI : SigmaFinite (μ.comap ((↑) : H → G)) := by
    refine SigmaFinite.of_map _ he.measurable.aemeasurable ?_
    rw [hmap]
    exact hσ
  haveI : IsMulLeftInvariant (μ.comap ((↑) : H → G)) := by
    constructor
    intro g
    have hm1 : Measurable (fun x : H => g * x) := measurable_const_mul g
    have hm2 : Measurable (fun x : G => (g : G) * x) := measurable_const_mul (g : G)
    have key : ((μ.comap ((↑) : H → G)).map (fun x : H => g * x)).map ((↑) : H → G) = μ := by
      rw [Measure.map_map he.measurable hm1]
      have hcomp : ((↑) : H → G) ∘ (fun x : H => g * x) = (fun x : G => (g : G) * x) ∘ ((↑) : H → G) := rfl
      rw [hcomp, ← Measure.map_map hm2 he.measurable, hmap]
      exact hinv g g.2
    rw [← he.comap_map ((μ.comap ((↑) : H → G)).map (fun x : H => g * x)), key]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have hKpos : (Measure.haar : Measure H) K ≠ 0 := by
    first
      | exact (measure_pos_of_mem_nhds _ hK1).ne'
      | exact (measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hKfin : (Measure.haar : Measure H) K < ⊤ := hK.measure_lt_top
  obtain ⟨n, hn⟩ : ∃ n, (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hKpos
    have hU : K = ⋃ n, K ∩ spanningSets (μ.comap ((↑) : H → G)) n := by
      rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
    rw [hU]
    exact measure_iUnion_null hcon
  have hsm : MeasurableSet (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) :=
    hK.measurableSet.inter (measurableSet_spanningSets _ n)
  have hsfin : (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKfin).ne
  have hνfin : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top _ n)).ne
  haveI : BorelSpace H := by
    first
      | infer_instance
      | exact Subtype.borelSpace _
  haveI : SecondCountableTopology H := by
    first
      | infer_instance
      | exact TopologicalSpace.Subtype.secondCountableTopology _
  haveI : MeasurableMul₂ H := by
    first
      | infer_instance
      | exact ContinuousMul.measurableMul₂
  haveI : MeasurableInv H := by
    first
      | infer_instance
      | exact ContinuousInv.measurableInv
  have heq := measure_eq_div_smul (μ.comap ((↑) : H → G)) (Measure.haar : Measure H) hn hsfin
  have hc0 : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) /
      (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ 0 := by
    intro h
    rw [h, zero_smul] at heq
    apply h0
    rw [← hmap, heq, Measure.map_zero]
  have hctop : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) /
      (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤ :=
    (ENNReal.div_lt_top hνfin hn).ne
  have hHaar : (μ.comap ((↑) : H → G)).IsHaarMeasure := by
    rw [heq]
    first
      | exact Measure.isHaarMeasure_smul _ hc0 hctop
      | exact IsHaarMeasure.smul _ hc0 hctop
      | exact isHaarMeasure_smul _ hc0 hctop
  haveI := hHaar
  refine ⟨hHaar, fun K' hK' => ?_, fun U hU hne => ?_⟩
  · rw [← hmap, he.map_apply]
    exact (hce.isCompact_preimage hK').measure_lt_top
  · obtain ⟨x, hxU, hxH⟩ := hne
    rw [← hmap, he.map_apply]
    exact (hU.preimage continuous_subtype_val).measure_pos _ ⟨⟨x, hxH⟩, hxU⟩

end Abs

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

theorem haarOnSet_isHaar_inst (H : Subgroup I.Ginf) (hH : IsClosed (H : Set I.Ginf)) (μ : Measure I.Ginf)
    (h : Formalism.L2.SG.HidaSetting.IsHaarOnSet I (H : Set I.Ginf) μ) :
    (μ.comap ((↑) : H → I.Ginf)).IsHaarMeasure ∧ (∀ K : Set I.Ginf, IsCompact K → μ K < ⊤) ∧
      ∀ U : Set I.Ginf, IsOpen U → (U ∩ (H : Set I.Ginf)).Nonempty → 0 < μ U := by
  exact haarOnSet_isHaar H hH μ h.1 h.2.1 h.2.2.1 h.2.2.2

end Inst

end Formalism.L2.SG.Pf
