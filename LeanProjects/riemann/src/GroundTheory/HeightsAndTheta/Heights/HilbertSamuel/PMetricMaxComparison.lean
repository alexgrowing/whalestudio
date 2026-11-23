import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricMaxComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem MetricMaxComparison.proof : MetricMaxComparison.Statement := by
  intro K _ ι _ A hA

  let blk : (k : K) → ((Σ k, ι k) → ℂ) → (ι k → ℂ) := fun k z i => z ⟨k, i⟩
  have hblkc : ∀ k, Continuous (blk k) := fun k => continuous_pi fun i => continuous_apply _
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖blk k z‖ = 1}
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hS : S = ⋂ k, (fun z => ‖blk k z‖) ⁻¹' {1} := by ext z; simp [S]
      rw [hS]
      exact isClosed_iInter fun k => isClosed_singleton.preimage (hblkc k).norm
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro p
      calc ‖z p‖ = ‖blk p.1 z p.2‖ := rfl
        _ ≤ ‖blk p.1 z‖ := norm_le_pi_norm _ _
        _ = 1 := hz p.1
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : blk k z = 0 := funext h
    have h1 : ‖blk k z‖ = 1 := hz k
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨C0, hC0⟩ := hSc.exists_bound_of_continuousOn (hA.continuousOn.mono hSU)
  refine ⟨max C0 1, le_max_right _ _, fun z hz => ?_⟩
  have hn : ∀ k, 0 < ‖blk k z‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact norm_pos_iff.mpr fun h0 => hi (congrFun h0 i)
  let c : K → ℂ := fun k => ((‖blk k z‖⁻¹ : ℝ) : ℂ)
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (hn k).ne'
  have hcn : ∀ k, ‖c k‖ = ‖blk k z‖⁻¹ := fun k => by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (hn k))
  have hwS : (fun p : Σ k, ι k => c p.1 * z p) ∈ S := fun k => by
    have h1 : blk k (fun p : Σ k, ι k => c p.1 * z p) = c k • blk k z := rfl
    rw [h1, norm_smul, hcn, inv_mul_cancel₀ (hn k).ne']
  have hmax : (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z = ∏ k, ‖blk k z‖ ^ A.a k := rfl
  have hprod : (∏ k, ‖blk k z‖ ^ A.a k) * (∏ k, ‖c k‖ ^ A.a k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcn, ← mul_zpow, mul_inv_cancel₀ (hn k).ne', one_zpow]
  have hz' : A.h z = (∏ k, ‖blk k z‖ ^ A.a k) * A.h (fun p : Σ k, ι k => c p.1 * z p) := by
    rw [A.smul c z hc0, ← mul_assoc, hprod, one_mul]
  have hpos : 0 ≤ ∏ k, ‖blk k z‖ ^ A.a k :=
    Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
  have hbw : A.h (fun p : Σ k, ι k => c p.1 * z p) ≤ max C0 1 := by
    have h1 := hC0 _ hwS
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  rw [hmax, hz', mul_comm (max C0 1)]
  exact mul_le_mul_of_nonneg_left hbw hpos

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
