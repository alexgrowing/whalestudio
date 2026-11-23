import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

namespace GlobalTheory.FrechetDerivativeBound

theorem norm_fderiv_le_of_bounded_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {ρ R M : ℝ} (hρ : 0 < ρ) (hR : ρ < R) (u : E → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ := by
  have hp : p ∈ Metric.ball p R := Metric.mem_ball_self (hρ.trans hR)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM0 hρ.le) ?_
  intro v hv
  have hmem : ∀ t ∈ Metric.closedBall (0 : ℂ) ρ, p + t • v ∈ Metric.ball p R := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]
    exact ht.trans_lt hR
  have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => p + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hd : DifferentiableOn ℂ (fun t : ℂ => u (p + t • v)) (Metric.closedBall 0 ρ) :=
    hu.comp (fun t _ => (hline t).differentiableAt.differentiableWithinAt) hmem
  have hdc : DiffContOnCl ℂ (fun t : ℂ => u (p + t • v)) (Metric.ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ hρ.ne']
  have hup : DifferentiableAt ℂ u p := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hp)
  have hder : HasDerivAt (fun t : ℂ => u (p + t • v)) (fderiv ℂ u p v) 0 := by
    have h1 : HasFDerivAt u (fderiv ℂ u p) (p + (0 : ℂ) • v) := by
      simpa using hup.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hline 0)
  rw [← hder.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc
    (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))

theorem norm_fderiv_le_of_bounded {n : ℕ} {p : ReciprocityTheory.L2DbarEstimates.V n} {ρ R M : ℝ}
    (hρ : (0 : ℝ) < ρ) (hR : ρ < R) (u : ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ :=
  norm_fderiv_le_of_bounded_gen hρ hR u hu hM

end GlobalTheory.FrechetDerivativeBound
