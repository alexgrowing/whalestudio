import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem kerSwap : KerUnif → KerSwap := by
  intro hU H _ _ _ _ _ _ _ _ n ι hι μ _ Ω I _ _ m _ c q hk P _ _ _ W p K C hW hp hK hC hWC
  obtain ⟨B, hB⟩ := hU H n ι hι Ω I m c q hk P W p K C hW hp hK hC hWC
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hmc : Continuous (matCoord ι) := hι.continuous
  set G : H × H → ℂ := fun z => W (matCoord ι z.1, p z.2) with hG
  have hGc : Continuous G := hW.continuous.comp ((hmc.comp continuous_fst).prodMk (hp.comp continuous_snd))
  set F : H → Ω → ℂ := fun k x => ker c q (fun y => W (matCoord ι y, p k)) x with hF

  have hvan : ∀ x, ∀ k ∈ K, ∀ i, i ∉ (hk.fin x C hC).toFinset → c i x * W (matCoord ι (q i x), p k) = 0 := by
    intro x k hkK i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
    rcases hi with h | h
    · simp [h]
    · simp [hWC k hkK _ h]

  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict K).prod m) := by
    obtain ⟨u, hu⟩ := (atTop : Filter (Finset I)).exists_seq_tendsto
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N (z : H × Ω) => ∑ i ∈ u N, c i z.2 * W (matCoord ι (q i z.2), p z.1)) ?_ ?_
    · intro N
      refine (Finset.measurable_sum _ fun i _ => ?_).aestronglyMeasurable
      refine ((hk.mc i).comp measurable_snd).mul ?_
      have : Measurable fun z : H × Ω => ((q i z.2, z.1) : H × H) :=
        ((hk.mq i).comp measurable_snd).prodMk measurable_fst
      exact hGc.measurable.comp this
    · have hae : ∀ᵐ z ∂((μ.restrict K).prod m), z.1 ∈ K :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_restrict_mem hKm)
      filter_upwards [hae] with z hz
      have hs : HasSum (fun i => c i z.2 * W (matCoord ι (q i z.2), p z.1))
          (∑' i, c i z.2 * W (matCoord ι (q i z.2), p z.1)) :=
        (summable_of_ne_finset_zero (s := (hk.fin z.2 C hC).toFinset) (hvan z.2 z.1 hz)).hasSum
      exact hs.comp hu
  have hint : Integrable (Function.uncurry F) ((μ.restrict K).prod m) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hKm] with k hkK
      exact (hB k hkK).1
    · refine Integrable.mono' (integrable_const B) hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hKm] with k hkK
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hB k hkK).2
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF, ker]
  have hT := hvan x
  set T := (hk.fin x C hC).toFinset
  rw [setIntegral_congr_fun hKm (fun k hkK => tsum_eq_sum (s := T) (hT k hkK))]
  rw [integral_finsetSum]
  · rw [tsum_eq_sum (s := T)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_const_mul _ _
    · intro i hi
      simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
      rcases hi with h | h
      · simp [h]
      · rw [setIntegral_eq_zero_of_forall_eq_zero (fun k hkK => hWC k hkK _ h), mul_zero]
  · intro i _
    exact (ContinuousOn.integrableOn_compact hK
      (continuous_const.mul (hW.continuous.comp (continuous_const.prodMk hp))).continuousOn)

end MainStatements.WeightKernel
