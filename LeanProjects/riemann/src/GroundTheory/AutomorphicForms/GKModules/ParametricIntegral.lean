import Mathlib

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {α : Type*} [TopologicalSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

namespace ParamIntegral

variable (F : P → α → F')

noncomputable def iter (k : ℕ) (Y : P) (a : α) : ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F' :=
  iteratedFDeriv ℝ k (fun Y => F Y a) Y

variable {F}

theorem iter_eq_zero_of_eventually {k : ℕ} {Y : P} {a : α} (h : ∀ᶠ Y' in 𝓝 Y, F Y' a = 0) :
    iter F k Y a = 0 := by
  have : (fun Y' => F Y' a) =ᶠ[𝓝 Y] fun _ => (0 : F') := h
  rw [iter, (this.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  simp

theorem fderiv_iter (k : ℕ) (Y : P) (a : α) :
    fderiv ℝ (fun Y => iter F k Y a) Y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F' (iter F (k + 1) Y a) := by
  simp [iter, iteratedFDeriv_succ_eq_comp_left]

end ParamIntegral

open ParamIntegral

set_option synthInstance.maxHeartbeats 200000 in

theorem hasFDerivAt_integral_iter (F : P → α → F')
    (hF : ∀ a, ContDiff ℝ ∞ (fun Y => F Y a))
    (hcont : ∀ k : ℕ, Continuous (fun p : P × α => iter F k p.1 p.2))
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0)
    (k : ℕ) (Y₀ : P) :
    HasFDerivAt (fun Y => ∫ a, iter F k Y a ∂μ)
      (∫ a, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F'
        (iter F (k + 1) Y₀ a) ∂μ) Y₀ := by
  obtain ⟨U, hU, C, hC, hFC⟩ := hsupp Y₀
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU

  have hzero : ∀ j : ℕ, ∀ Y ∈ ball Y₀ r, ∀ a ∉ C, iter F j Y a = 0 := by
    intro j Y hY a ha
    refine iter_eq_zero_of_eventually ?_
    filter_upwards [isOpen_ball.mem_nhds hY] with Y' hY'
    exact hFC Y' (hrU hY') a ha
  have hcpt : ∀ j : ℕ, ∀ Y : P, Y ∈ ball Y₀ r → HasCompactSupport (iter F j Y) := fun j Y hY =>
    HasCompactSupport.intro hC fun a ha => hzero j Y hY a ha
  have hcY : ∀ j : ℕ, ∀ Y : P, Continuous (iter F j Y) := fun j Y =>
    (hcont j).comp (Continuous.prodMk_right Y)

  have hK : IsCompact (closedBall Y₀ (r / 2) ×ˢ C) := (isCompact_closedBall Y₀ _).prod hC
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont (k + 1)).continuousOn
  have hsub : ball Y₀ (r / 2) ⊆ ball Y₀ r := ball_subset_ball (by linarith)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := C.indicator fun _ => M)
    (F' := fun Y a => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F'
      (iter F (k + 1) Y a)) (ball_mem_nhds Y₀ (half_pos hr))
    (Eventually.of_forall fun Y => (hcY k Y).aestronglyMeasurable)
    ((hcY k Y₀).integrable_of_hasCompactSupport (hcpt k Y₀ (mem_ball_self hr)))
    ((LinearIsometryEquiv.continuous _).comp (hcY (k + 1) Y₀)).aestronglyMeasurable ?_ ?_ ?_
  · refine Eventually.of_forall fun a Y hY => ?_
    rw [LinearIsometryEquiv.norm_map]
    by_cases ha : a ∈ C
    · rw [indicator_of_mem ha]
      exact hM (Y, a) ⟨ball_subset_closedBall hY, ha⟩
    · rw [indicator_of_notMem ha, hzero (k + 1) Y (hsub hY) a ha, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)
  · refine Eventually.of_forall fun a Y _ => ?_
    rw [← fderiv_iter]
    have hd : Differentiable ℝ (fun Y => iter F k Y a) :=
      (hF a).differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    exact (hd Y).hasFDerivAt

theorem iteratedFDeriv_integral_eq (F : P → α → F')
    (hF : ∀ a, ContDiff ℝ ∞ (fun Y => F Y a))
    (hcont : ∀ k : ℕ, Continuous (fun p : P × α => iter F k p.1 p.2))
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0)
    (k : ℕ) :
    iteratedFDeriv ℝ k (fun Y => ∫ a, F Y a ∂μ) = fun Y => ∫ a, iter F k Y a ∂μ := by
  induction k with
  | zero =>
    funext Y
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    simp only [iter, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ P F').symm.toContinuousLinearEquiv.integral_comp_comm
      (fun a => F Y a)).symm
  | succ k ih =>
    funext Y
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih,
      (hasFDerivAt_integral_iter F hF hcont hsupp k Y).fderiv]
    have e := LinearIsometry.integral_comp_comm (μ := μ) (𝕜 := ℝ)
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => P) F')
      (F := P →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F')
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F').toLinearIsometry
      (fun a => iter F (k + 1) Y a)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at e
    rw [e]
    simp

theorem contDiff_integral_of_iteratedFDeriv (F : P → α → F')
    (hF : ∀ a, ContDiff ℝ ∞ (fun Y => F Y a))
    (hcont : ∀ k : ℕ, Continuous (fun p : P × α => iter F k p.1 p.2))
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0) :
    ContDiff ℝ ∞ (fun Y => ∫ a, F Y a ∂μ) := by
  refine contDiff_of_differentiable_iteratedFDeriv fun k _ => ?_
  rw [iteratedFDeriv_integral_eq F hF hcont hsupp k]
  exact fun Y => (hasFDerivAt_integral_iter F hF hcont hsupp k Y).differentiableAt

end GroundTheory.Automorphic
