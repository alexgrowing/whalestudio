import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory Topology
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Convcont

theorem shift (X : Ctx) (φ u : X.G → ℂ) (x : X.G) :
    ∫ y, φ y * u (x * y) ∂X.μ = ∫ z, φ (x⁻¹ * z) * u z ∂X.μ := by
  have := integral_mul_left_eq_self (μ := X.μ) (fun z => φ (x⁻¹ * z) * u z) x
  simp only [inv_mul_cancel_left] at this
  exact this

end Convcont

open Convcont in
theorem convcont : ConvCont := by
  intro X φ u hφ hu
  have hfun : (fun x => ∫ y, φ y * u (x * y) ∂X.μ) = fun x => ∫ z, φ (x⁻¹ * z) * u z ∂X.μ :=
    funext fun x => shift X φ u x
  rw [hfun]
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  have hK : IsCompact (N * tsupport φ) := hNc.mul hφ.2
  have hcx : ∀ z : X.G, Continuous fun x : X.G => φ (x⁻¹ * z) :=
    fun z => hφ.1.comp (continuous_inv.mul continuous_const)
  refine continuousAt_of_dominated (bound := (N * tsupport φ).indicator fun z => B * ‖u z‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul hu.aestronglyMeasurable
  · filter_upwards [hN] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ N * tsupport φ
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hz]
      have h0 : φ (x⁻¹ * z) = 0 := by
        by_contra h
        apply hz
        refine ⟨x, hx, x⁻¹ * z, subset_tsupport _ h, ?_⟩
        simp
      simp [h0]
  · rw [integrable_indicator_iff hK.measurableSet]
    exact ((hu.integrableOn_isCompact hK).norm.const_mul B)
  · exact Filter.Eventually.of_forall fun z => ((hcx z).mul continuous_const).continuousAt

end PositivityTheory.Rg.BcB.E2.P
