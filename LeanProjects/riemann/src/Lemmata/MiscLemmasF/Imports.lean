import Mathlib
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace Bl.SecondBlockLemmaG

theorem goal1 :
  ∀ {n : Nat} {Ω K : Set.{0} (ReciprocityTheory.L2DbarEstimates.C.V n)} {u : ReciprocityTheory.L2DbarEstimates.C.V n → Complex},
  IsOpen.{0} Ω →
    DifferentiableOn.{0, 0, 0} Complex u Ω →
      IsCompact.{0} K →
        LE.le.{0} K Ω →
          ∀ (v : ReciprocityTheory.L2DbarEstimates.C.V n),
            Exists.{1} fun (C : Real) ↦
              ∀ (x : ReciprocityTheory.L2DbarEstimates.C.V n),
                Membership.mem.{0, 0} K x →
                  LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (fderiv.{0, 0, 0} Real u x) v)) C := by
  intro n Ω K u hΩ hu hK hKΩ v
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨M, hM⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn
    (hu.continuousOn.mono hδΩ)
  by_cases hv : v = 0
  · refine ⟨0, fun x _ => ?_⟩
    simp [hv]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨M / (δ / ‖v‖), fun x hx => ?_⟩
    have hr : 0 < δ / ‖v‖ := div_pos hδ hvpos
    have hux : DifferentiableAt ℂ u x :=
      (hu x (hKΩ hx)).differentiableAt (hΩ.mem_nhds (hKΩ hx))
    have hR : fderiv ℝ u x v = fderiv ℂ u x v := by
      rw [(hux.hasFDerivAt.restrictScalars ℝ).fderiv]
      rfl
    have hmem : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) (δ / ‖v‖) →
        x + z • v ∈ Metric.cthickening δ K := by
      intro z hz
      apply Metric.closedBall_subset_cthickening hx
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      calc ‖z‖ * ‖v‖ ≤ δ / ‖v‖ * ‖v‖ := by gcongr
        _ = δ := div_mul_cancel₀ δ hvpos.ne'
    have hgd : DifferentiableOn ℂ (fun z : ℂ => u (x + z • v))
        (Metric.closedBall (0 : ℂ) (δ / ‖v‖)) := by
      intro z hz
      have h1 : DifferentiableAt ℂ u (x + z • v) :=
        (hu _ (hδΩ (hmem z hz))).differentiableAt (hΩ.mem_nhds (hδΩ (hmem z hz)))
      have h2 : DifferentiableAt ℂ (fun w : ℂ => x + w • v) z :=
        (differentiableAt_id.smul_const v).const_add x
      exact (h1.comp z h2).differentiableWithinAt
    have hdc := hgd.diffContOnCl_ball subset_rfl
    have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
      (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))
    have hderiv : HasDerivAt (fun z : ℂ => u (x + z • v)) (fderiv ℂ u x v) 0 := by
      have h2 : HasDerivAt (fun w : ℂ => x + w • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
      have h1 : HasFDerivAt u (fderiv ℂ u x) (x + (0 : ℂ) • v) := by
        simpa using hux.hasFDerivAt
      exact h1.comp_hasDerivAt 0 h2
    rw [hR, ← hderiv.deriv]
    exact hest

end Bl.SecondBlockLemmaG
