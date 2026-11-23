import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal

namespace QPK

def toSub {G : Type} [Group G] (K : Set G) (hK : IsGrp K) : Subgroup G where
  carrier := K
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2 _ ha

section Sub

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

lemma map_val_mul (K' : Subgroup G) (g : K') (α : Measure K') :
    (α.map (fun x => g * x)).map Subtype.val = (α.map Subtype.val).map (fun x => (g : G) * x) := by
  have hv : Measurable (Subtype.val : K' → G) := measurable_subtype_coe
  have hm : Measurable (fun x : K' => g * x) := by
    have h : Measurable (fun x : K' => (g : G) * (x : G)) := (measurable_const_mul (g : G)).comp hv
    exact h.subtype_mk
  rw [Measure.map_map hv hm, Measure.map_map (measurable_const_mul _) hv]
  rfl

end Sub

theorem haar_measure_existence : HaarExist := by
  intro G _ _ _ _ _ _ _ _ K hKc hK
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : H → G) := hHc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace H := hemb.locallyCompactSpace
  have hv : Measurable (Subtype.val : H → G) := measurable_subtype_coe
  let α : Measure H := Measure.haar
  have hfin : IsFiniteMeasureOnCompacts (α.map Subtype.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [Measure.map_apply hv hC.isClosed.measurableSet]
    exact (hemb.isCompact_preimage hC).measure_lt_top
  refine ⟨α.map Subtype.val, ⟨?_, ?_, ?_, ?_⟩, hfin, ?_⟩
  · infer_instance
  · intro h
    rw [Measure.map_eq_zero_iff hv.aemeasurable] at h
    exact (Measure.measure_univ_pos.mp (isOpen_univ.measure_pos α Set.univ_nonempty)) h
  · rw [Measure.map_apply hv hKc.measurableSet.compl]
    have h : (Subtype.val : H → G) ⁻¹' Kᶜ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2
    rw [h, measure_empty]
  · intro s hs
    have h := map_val_mul H ⟨s, hs⟩ α
    rw [map_mul_left_eq_self] at h
    exact h.symm
  · intro U hU ⟨x, hxU, hxK⟩
    rw [Measure.map_apply hv hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_ne_zero α ⟨⟨x, hxK⟩, hxU⟩

theorem haar_measure_uniqueness : HaarUniq := by
  intro G _ _ _ _ _ _ _ _ K hKc hK μ ν hμ hν
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hme : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hKc.measurableSet
  let K₀ : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have key : ∀ ρ : Measure G, InvOn ρ K → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
    intro ρ ⟨hσ, h0, hc, hinv⟩
    let ρ' : Measure H := ρ.comap Subtype.val
    have hback : ρ'.map Subtype.val = ρ := by
      rw [hme.map_comap, Subtype.range_coe]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)
    haveI : SigmaFinite ρ' :=
      SigmaFinite.of_map ρ' hme.measurable.aemeasurable (by rw [hback]; exact hσ)
    haveI : IsMulLeftInvariant ρ' := by
      refine ⟨fun g => ?_⟩
      calc ρ'.map (g * ·) = ((ρ'.map (g * ·)).map Subtype.val).comap Subtype.val :=
            (hme.comap_map _).symm
        _ = ((ρ'.map Subtype.val).map ((g : G) * ·)).comap Subtype.val := by rw [map_val_mul]
        _ = ρ' := by rw [hback, hinv (g : G) g.2]
    obtain ⟨c, hK0⟩ : ∃ c : ℝ≥0∞, ρ' = c • Measure.haarMeasure K₀ :=
      ⟨_, Measure.haarMeasure_unique ρ' K₀⟩
    have hρ : ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
      rw [← hback, hK0, Measure.map_smul]
    refine ⟨c, ?_, ?_, hρ⟩
    · intro hz
      apply h0
      rw [hρ, hz, zero_smul]
    · intro htop
      have hne : Measure.haarMeasure K₀ (⋃ n, spanningSets ρ' n) ≠ 0 := by
        rw [iUnion_spanningSets]
        exact (lt_of_lt_of_le zero_lt_one
          ((Measure.haarMeasure_self (K₀ := K₀)).symm.le.trans (measure_mono (Set.subset_univ _)))).ne'
      obtain ⟨n, hn⟩ : ∃ n, Measure.haarMeasure K₀ (spanningSets ρ' n) ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hne (measure_iUnion_null_iff.2 hall)
      have h2 : ρ' (spanningSets ρ' n) = (c • Measure.haarMeasure K₀) (spanningSets ρ' n) :=
        congrArg (fun m : Measure H => m (spanningSets ρ' n)) hK0
      have h3 := measure_spanningSets_lt_top ρ' n
      rw [h2, Measure.smul_apply, htop, smul_eq_mul, ENNReal.top_mul hn] at h3
      exact lt_irrefl _ h3
  obtain ⟨a, ha0, hat, hμ'⟩ := key μ hμ
  obtain ⟨b, hb0, hbt, hν'⟩ := key ν hν
  refine ⟨a / b, (ENNReal.div_pos ha0 hbt).ne', ENNReal.div_ne_top hat hb0, ?_⟩
  rw [hμ', hν', smul_smul, ENNReal.div_mul_cancel hb0 hbt]

end QPK
