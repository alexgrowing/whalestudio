import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

open Metric

namespace GlobalTheory

theorem norm_fderiv_le_of_closedBall_subset {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {U : Set H} {f : H → ℂ} {C r : ℝ} {y : H} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hy : closedBall y r ⊆ U) (hC : ∀ x ∈ U, ‖f x‖ ≤ C) :
    ‖fderiv ℂ f y‖ ≤ C / r := by
  have hyU : y ∈ U := hy (mem_closedBall_self hr.le)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y hyU)
  refine ContinuousLinearMap.opNorm_le_bound' _ (div_nonneg hC0 hr.le) fun v hv => ?_
  have hv0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hR : 0 < r / ‖v‖ := div_pos hr hv0
  have hmem : ∀ t ∈ closedBall (0 : ℂ) (r / ‖v‖), y + t • v ∈ U := by
    intro t ht
    apply hy
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (le_div_iff₀ hv0).1 ht
  have hlin : ∀ t : ℂ, HasDerivAt (fun s : ℂ => y + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hd : DifferentiableOn ℂ (fun s : ℂ => f (y + s • v)) (closedBall 0 (r / ‖v‖)) := by
    intro t ht
    exact ((hf.differentiableAt (hU.mem_nhds (hmem t ht))).comp t
      (hlin t).differentiableAt).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun s : ℂ => f (y + s • v)) (ball 0 (r / ‖v‖)) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball _ hR.ne'])
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (sphere_subset_closedBall hz)))
  have hder : HasDerivAt (fun s : ℂ => f (y + s • v)) (fderiv ℂ f y v) 0 := by
    have h1 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using (hf.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hlin 0)
  rw [hder.deriv] at hb
  refine hb.trans (le_of_eq ?_)
  field_simp

theorem differentiableOn_tsum_of_norm_le :
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (ι : Type) (U : Set H)
      (f : ι → H → ℂ) (u : ι → ℝ), IsOpen U → (∀ i, DifferentiableOn ℂ (f i) U) → Summable u →
      (∀ i, ∀ x ∈ U, ‖f i x‖ ≤ u i) → DifferentiableOn ℂ (fun x => ∑' i, f i x) U := by
  intro H _ _ ι U f u hU hf hu hb x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : ∀ y ∈ ball x (ε / 2), closedBall y (ε / 2) ⊆ U := by
    intro y hy z hz
    apply hball
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  have h := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) (f := f)
    (f' := fun i y => fderiv ℂ (f i) y) (u := fun i => u i / (ε / 2)) (s := ball x (ε / 2))
    (x₀ := x) (x := x) (hu.div_const _) isOpen_ball (convex_ball x _).isPreconnected
    (fun i y hy => ((hf i).differentiableAt
      (hU.mem_nhds (hsub y hy (mem_closedBall_self hr.le)))).hasFDerivAt)
    (fun i y hy => norm_fderiv_le_of_closedBall_subset hU (hf i) hr (hsub y hy) (hb i))
    (mem_ball_self hr) (Summable.of_norm_bounded hu (fun i => hb i x hx)) (mem_ball_self hr)
  exact h.differentiableAt.differentiableWithinAt

end GlobalTheory
