import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open MeasureTheory

namespace GlobalTheory

theorem contDiffOn_one_injOn_ball_det_norm_bounds {d : ℕ} (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (v₀ : ReciprocityTheory.L2DbarEstimates.V d)
    (Ψ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (hU : IsOpen U) (hv₀ : v₀ ∈ U)
    (hΨ : ContDiffOn ℝ 1 Ψ U) (hbij : Function.Bijective (fderiv ℝ Ψ v₀)) :
    ∃ r J L : ℝ, 0 < r ∧ 0 < J ∧ 0 ≤ L ∧ Metric.ball v₀ r ⊆ U ∧ Set.InjOn Ψ (Metric.ball v₀ r) ∧
      ∀ v ∈ Metric.ball v₀ r, J ≤ |(fderiv ℝ Ψ v).det| ∧ ‖fderiv ℝ Ψ v‖ ≤ L := by
  have hUn : U ∈ nhds v₀ := hU.mem_nhds hv₀
  have hcd : ContDiffAt ℝ 1 Ψ v₀ := hΨ.contDiffAt hUn
  have hs : HasStrictFDerivAt Ψ (fderiv ℝ Ψ v₀) v₀ := hcd.hasStrictFDerivAt one_ne_zero
  let e : ReciprocityTheory.L2DbarEstimates.V d ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V d :=
    (LinearEquiv.ofBijective ((fderiv ℝ Ψ v₀ : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) :
      ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ReciprocityTheory.L2DbarEstimates.V d) hbij).toContinuousLinearEquiv
  have he : (e : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) = fderiv ℝ Ψ v₀ := by
    ext x; rfl
  have hs' : HasStrictFDerivAt Ψ (e : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) v₀ := by
    rw [he]; exact hs
  set P := hs'.toOpenPartialHomeomorph Ψ with hP
  have hsrc : P.source ∈ nhds v₀ :=
    P.open_source.mem_nhds (hs'.mem_toOpenPartialHomeomorph_source)
  have hinj : Set.InjOn Ψ P.source := by
    have := P.injOn
    simpa [hP, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using this
  have hcont : ContinuousOn (fderiv ℝ Ψ) U := hΨ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hca : ContinuousAt (fderiv ℝ Ψ) v₀ := hcont.continuousAt hUn
  have hdet0 : (fderiv ℝ Ψ v₀).det ≠ 0 := by
    have := (LinearEquiv.ofBijective ((fderiv ℝ Ψ v₀ : ReciprocityTheory.L2DbarEstimates.V d →L[ℝ] ReciprocityTheory.L2DbarEstimates.V d) :
      ReciprocityTheory.L2DbarEstimates.V d →ₗ[ℝ] ReciprocityTheory.L2DbarEstimates.V d) hbij).isUnit_det'
    exact this.ne_zero
  set J : ℝ := |(fderiv ℝ Ψ v₀).det| / 2 with hJ
  have hJpos : 0 < J := by positivity
  have hdc : ContinuousAt (fun v => |(fderiv ℝ Ψ v).det|) v₀ :=
    (continuous_abs.comp ContinuousLinearMap.continuous_det).continuousAt.comp hca
  have ev1 : ∀ᶠ v in nhds v₀, J < |(fderiv ℝ Ψ v).det| :=
    hdc.eventually (lt_mem_nhds (by rw [hJ]; linarith [abs_pos.mpr hdet0]))
  have hnc : ContinuousAt (fun v => ‖fderiv ℝ Ψ v‖) v₀ := continuous_norm.continuousAt.comp hca
  have ev2 : ∀ᶠ v in nhds v₀, ‖fderiv ℝ Ψ v‖ < ‖fderiv ℝ Ψ v₀‖ + 1 :=
    hnc.eventually (gt_mem_nhds (by linarith))
  have ev : ∀ᶠ v in nhds v₀, (v ∈ U ∧ v ∈ P.source) ∧ (J < |(fderiv ℝ Ψ v).det| ∧
      ‖fderiv ℝ Ψ v‖ < ‖fderiv ℝ Ψ v₀‖ + 1) :=
    (Filter.Eventually.and hUn hsrc).and (ev1.and ev2)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp ev
  refine ⟨r, J, ‖fderiv ℝ Ψ v₀‖ + 1, hr, hJpos, by positivity, fun v hv => (hball v hv).1.1, ?_, ?_⟩
  · exact hinj.mono (fun v hv => (hball v hv).1.2)
  · intro v hv
    exact ⟨(hball v hv).2.1.le, (hball v hv).2.2.le⟩

end GlobalTheory
