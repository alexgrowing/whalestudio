import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.E2.P

namespace Locint

theorem enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

end Locint

theorem locint : Tonelli → LocInt := by
  intro hT X S _ ν _ F f hF hrep
  let K := CompactExhaustion.choice X.G
  have hfin : ∀ n, ∀ᵐ s ∂ν, ∫⁻ y, (K n).indicator 1 y * ‖f y s‖ₑ ^ 2 ∂X.μ < ⊤ := by
    intro n
    have hK : IsCompact (K n) := K.isCompact n
    have hW : Measurable ((K n).indicator (1 : X.G → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    apply hT X.G S X.μ ν F f _ hrep hW
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
    refine ne_top_of_le_ne_top (b := ∫⁻ y, (K n).indicator (fun _ => ENNReal.ofReal C ^ 2) y ∂X.μ) ?_ ?_
    · rw [lintegral_indicator_const hK.measurableSet]
      exact ENNReal.mul_ne_top (by simp) hK.measure_lt_top.ne
    · refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ K n
      · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC y hy)
      · simp [Set.indicator_of_notMem hy]
  rw [← ae_all_iff] at hfin
  filter_upwards [hfin] with s hs
  have hm : Measurable fun y => f y s := hrep.1.of_uncurry_right
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hk
  refine IntegrableOn.mono_set ?_ hn
  have hKn : IsCompact (K n) := K.isCompact n
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have heq : (fun y => (K n).indicator 1 y * ‖f y s‖ₑ ^ 2) = (K n).indicator (fun y => ‖f y s‖ₑ ^ 2) := by
    ext y; by_cases hy : y ∈ K n <;> simp [hy]
  have h2 := hs n
  rw [heq, lintegral_indicator hKn.measurableSet] at h2
  show ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) < ⊤
  calc ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) ≤ ∫⁻ y, (1 + ‖f y s‖ₑ ^ 2) ∂(X.μ.restrict (K n)) :=
        lintegral_mono fun y => Locint.enorm_le_one_add_sq _
    _ = X.μ (K n) + ∫⁻ y, ‖f y s‖ₑ ^ 2 ∂(X.μ.restrict (K n)) := by
        rw [lintegral_add_left measurable_const]; simp
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hKn.measure_lt_top, h2⟩

end PositivityTheory.Rg.BcB.E2.P

end
