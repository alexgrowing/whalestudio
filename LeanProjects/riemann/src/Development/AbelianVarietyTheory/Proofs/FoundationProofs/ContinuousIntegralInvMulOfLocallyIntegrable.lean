import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact

open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped Pointwise Topology

namespace GlobalTheory.AutomorphicL2Local

theorem continuous_integral_inv_mul_of_locallyIntegrable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} {f φ : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : LocallyIntegrable φ μ) :
    (∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ) ∧ Continuous fun x => ∫ y, f (x⁻¹ * y) * φ y ∂μ := by
  have hi : ∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ := fun x =>
    hφ.integrable_smul_left_of_hasCompactSupport (g := fun y => f (x⁻¹ * y)) (by fun_prop)
      (hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  refine ⟨hi, continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hK : IsCompact (U * tsupport f) := hU.mul hc.isCompact
  refine continuousAt_of_dominated (bound := (U * tsupport f).indicator fun y => M * ‖φ y‖)
    (.of_forall fun x => (hi x).1) ?_ ?_ (.of_forall fun y => ?_)
  · filter_upwards [hx] with x hxU
    refine .of_forall fun y => ?_
    by_cases hy : y ∈ U * tsupport f
    · rw [Set.indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy,
        image_eq_zero_of_notMem_tsupport (f := f) fun h => hy ⟨x, hxU, _, h, by simp⟩]
      simp
  · exact (integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M)
  · exact Continuous.continuousAt (by fun_prop)

theorem continuous_convR_lift : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ F : L2 Γ μ, (∀ x, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧ Continuous (convR μ f (lift Γ F)) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F
  have hφ : LocallyIntegrable (lift Γ F) μ :=
    locallyIntegrable_iff.2 fun C hC => (memLp_restrict_compact G Γ μ F C hC).2
  obtain ⟨h1, h2⟩ := continuous_integral_inv_mul_of_locallyIntegrable hf hc hφ
  refine ⟨fun x => ?_, h2.congr fun x => (convR_eq f _ x).symm⟩
  simpa using (h1 x).comp_mul_left x

end GlobalTheory.AutomorphicL2Local
