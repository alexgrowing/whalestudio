import Mathlib

noncomputable section

open MeasureTheory Filter Metric Complex
open scoped Topology NNReal ENNReal Real

namespace PositivityTheory.Rg.Rsw.L.LCfRel

section Circle

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem circle_swap (ν : Measure X) [IsFiniteMeasure ν] (f : ℂ → X → ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn (fun p : ℂ × X => f p.1 p.2) (sphere c R ×ˢ Set.univ)) {M : ℝ}
    (hM : ∀ z ∈ sphere c R, ∀ x, ‖f z x‖ ≤ M) :
    (∮ z in C(c, R), ∫ x, f z x ∂ν) = ∫ x, (∮ z in C(c, R), f z x) ∂ν := by
  have h1 : Continuous fun p : ℝ × X => f (circleMap c R p.1) p.2 :=
    hf.comp_continuous (((continuous_circleMap c R).comp continuous_fst).prodMk continuous_snd)
      fun p => ⟨circleMap_mem_sphere c hR p.1, Set.mem_univ _⟩
  have hG : Continuous fun p : ℝ × X => deriv (circleMap c R) p.1 • f (circleMap c R p.1) p.2 := by
    simp only [deriv_circleMap]
    exact (((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const).smul h1
  have hint : Integrable (Function.uncurry fun θ x => deriv (circleMap c R) θ • f (circleMap c R θ) x)
      ((volume.restrict (Set.Ioc 0 (2 * π))).prod ν) := by
    refine Integrable.of_bound hG.aestronglyMeasurable (R * M) (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, deriv_circleMap, smul_eq_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (hM _ (circleMap_mem_sphere c hR p.1) p.2) hR
  simp only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc ∫ θ in Set.Ioc 0 (2 * π), deriv (circleMap c R) θ • ∫ x, f (circleMap c R θ) x ∂ν
      = ∫ θ in Set.Ioc 0 (2 * π), ∫ x, deriv (circleMap c R) θ • f (circleMap c R θ) x ∂ν := by
        congr 1; ext θ; exact (integral_smul _ _).symm
    _ = _ := integral_integral_swap hint

theorem contOn_integral (ν : Measure X) [IsFiniteMeasure ν] (F : ℂ → X → ℂ) {s : Set ℂ}
    (hF : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (s ×ˢ Set.univ)) {M : ℝ} (hM : ∀ z ∈ s, ∀ x, ‖F z x‖ ≤ M) :
    ContinuousOn (fun z => ∫ x, F z x ∂ν) s := by
  refine continuousOn_of_dominated (bound := fun _ => M) (fun z hz => ?_) (fun z hz => ae_of_all _ (hM z hz))
    (integrable_const M) (ae_of_all _ fun x => ?_)
  · exact (hF.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩).aestronglyMeasurable
  · exact hF.comp (continuous_id.prodMk continuous_const).continuousOn fun z hz => ⟨hz, Set.mem_univ _⟩

theorem diffOn_integral (ν : Measure X) [IsFiniteMeasure ν] (F : ℂ → X → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hc : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (U ×ˢ Set.univ)) (hd : ∀ x, DifferentiableOn ℂ (F · x) U)
    (hb : ∀ S ⊆ U, IsCompact S → ∃ M, ∀ z ∈ S, ∀ x, ‖F z x‖ ≤ M) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂ν) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  let R : ℝ≥0 := ⟨r / 2, by positivity⟩
  have hR : (0 : ℝ) < R := by show 0 < r / 2; positivity
  have hsub : closedBall z₀ R ⊆ U := (closedBall_subset_ball (show (R : ℝ) < r by show r / 2 < r; linarith)).trans hrU
  obtain ⟨M, hM⟩ := hb _ hsub (isCompact_closedBall z₀ R)
  have hsph : sphere z₀ (R : ℝ) ⊆ closedBall z₀ R := sphere_subset_closedBall
  have hcont : ContinuousOn (fun z => ∫ x, F z x ∂ν) (sphere z₀ R) :=
    contOn_integral ν F (hc.mono (Set.prod_mono (hsph.trans hsub) le_rfl)) fun z hz => hM z (hsph hz)
  have hps := hasFPowerSeriesOn_cauchy_integral (hcont.circleIntegrable hR.le) (by exact_mod_cast hR)
  have key : ∀ w ∈ ball z₀ (R : ℝ), (∫ x, F w x ∂ν) =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν := by
    intro w hw
    have hinv : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere z₀ R) :=
      ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => sub_ne_zero.2 fun h => by
        rw [mem_sphere] at hz; rw [mem_ball, ← h, hz] at hw; exact lt_irrefl _ hw
    obtain ⟨B, hB⟩ := (isCompact_sphere z₀ (R : ℝ)).exists_bound_of_continuousOn hinv
    have hsw := circle_swap ν (fun z x => (z - w)⁻¹ • F z x) z₀ hR.le
      ((hinv.comp continuousOn_fst fun p hp => hp.1).smul (hc.mono (Set.prod_mono (hsph.trans hsub) le_rfl)))
      (M := B * M) fun z hz x => by
        rw [norm_smul]
        exact mul_le_mul (hB z hz) (hM z (hsph hz) x) (norm_nonneg _) ((norm_nonneg _).trans (hB z hz))
    have e1 : (∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν) = ∮ z in C(z₀, R), ∫ x, (z - w)⁻¹ • F z x ∂ν :=
      circleIntegral.integral_congr hR.le fun z _ => (integral_smul _ _).symm
    rw [e1, hsw]
    have e2 : ∀ x, (∮ z in C(z₀, R), (z - w)⁻¹ • F z x) = (2 * π * I : ℂ) • F w x := fun x =>
      ((hd x).mono hsub).circleIntegral_sub_inv_smul hw
    simp only [e2, integral_smul, smul_smul]
    rw [inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
  have hev : (fun z => ∫ x, F z x ∂ν) =ᶠ[𝓝 z₀]
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(z₀, R), (z - w)⁻¹ • ∫ x, F z x ∂ν) :=
    Filter.eventually_of_mem (ball_mem_nhds z₀ hR) key
  exact (hps.analyticAt.differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt

end Circle

theorem eqOn_right {U : Set ℂ} (hUo : IsOpen U) (hU : ∃ τ : ℝ, {z : ℂ | τ < z.re} ⊆ U) (hpc : IsPreconnected U)
    {h g : ℂ → ℂ} (hh : DifferentiableOn ℂ h U) (hg : DifferentiableOn ℂ g U) (σ : ℝ)
    (e : ∀ z : ℂ, σ < z.re → h z = g z) : Set.EqOn h g U := by
  obtain ⟨τ, hτ⟩ := hU
  have hx : max τ σ < (((max τ σ + 1 : ℝ)) : ℂ).re := by simp
  have hxU : (((max τ σ + 1 : ℝ)) : ℂ) ∈ U := hτ (lt_of_le_of_lt (le_max_left _ _) hx)
  have ev : h =ᶠ[𝓝 (((max τ σ + 1 : ℝ)) : ℂ)] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with w hw
    exact e w (lt_of_le_of_lt (le_max_right _ _) hw)
  exact (hh.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hpc hxU ev

theorem integral_tsum_dom {ι α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ι → α → ℂ) (u : ι → ℝ) (hu : Summable u) (hF : ∀ i a, ‖F i a‖ ≤ u i)
    (hm : ∀ i, AEStronglyMeasurable (F i) μ) :
    ∫ a, ∑' i, F i a ∂μ = ∑' i, ∫ a, F i a ∂μ := by
  have hs := hu.countable_support
  have : Countable (Function.support u) := hs.to_subtype
  have h0 : ∀ i, i ∉ Function.support u → ∀ a, F i a = 0 := fun i hi a => by
    have : u i = 0 := Function.notMem_support.1 hi
    exact norm_le_zero_iff.1 (this ▸ hF i a)
  have e1 : ∀ a, ∑' i, F i a = ∑' i : Function.support u, F i a := fun a =>
    (tsum_subtype_eq_of_support_subset fun i hi => by_contra fun h => hi (h0 i h a)).symm
  have e2 : ∑' i, ∫ a, F i a ∂μ = ∑' i : Function.support u, ∫ a, F i a ∂μ :=
    (tsum_subtype_eq_of_support_subset fun i hi => by_contra fun h => hi (by simp [h0 i h])).symm
  simp_rw [e1, e2]
  have hI : ∀ i, Integrable (F i) μ := fun i => Integrable.of_bound (hm i) (u i) (ae_of_all _ (hF i))
  refine (integral_tsum_of_summable_integral_norm (ι := Function.support u) (F := fun i a => F i a) (fun i => hI i) ?_).symm
  refine ((hu.subtype _).mul_right (μ.real Set.univ)).of_nonneg_of_le
    (fun i => integral_nonneg fun _ => norm_nonneg _) fun i => ?_
  calc ∫ a, ‖F i a‖ ∂μ ≤ ∫ _, u i ∂μ := integral_mono (hI i).norm (integrable_const _) fun a => hF i a
    _ = u i * μ.real Set.univ := by simp [mul_comm]

theorem circle_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → ℂ → ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ i ∈ s, ContinuousOn (g i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ s, a i * g i z) = ∑ i ∈ s, a i * ∮ z in C(c, R), g i z := by
  have hc : ∀ i ∈ s, Continuous fun θ => deriv (circleMap c R) θ • (a i * g i (circleMap c R θ)) := fun i hi => by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).mul continuous_const).smul (continuous_const.mul
      ((hg i hi).comp_continuous (continuous_circleMap c R) fun θ => circleMap_mem_sphere c hR θ))
  simp only [circleIntegral, Finset.smul_sum]
  rw [intervalIntegral.integral_finsetSum fun i hi => (hc i hi).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext θ; simp only [smul_eq_mul]; ring

end PositivityTheory.Rg.Rsw.L.LCfRel

end
