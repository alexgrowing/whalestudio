import Mathlib

open MeasureTheory Filter Metric Set
open scoped Topology Interval

namespace GlobalTheory

variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem aestronglyMeasurable_fderiv_apply_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) (v : E) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀ v) μ := by
  classical
  let f : ℂ → T → V := fun c t =>
    if AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ then
      c⁻¹ • (F t (x₀ + c • v) - F t x₀) else 0
  have h0 : AEStronglyMeasurable (fun t => F t x₀) μ := hmeas.self_of_nhds
  have hev : ∀ᶠ c : ℂ in 𝓝[≠] 0, AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ := by
    have hc : Tendsto (fun c : ℂ => x₀ + c • v) (𝓝 0) (𝓝 x₀) := by
      have : Continuous (fun c : ℂ => x₀ + c • v) := by fun_prop
      simpa using this.tendsto 0
    exact (hc.eventually hmeas).filter_mono nhdsWithin_le_nhds
  refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ)) (f := f) (fun c => ?_) ?_
  · by_cases h : AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ
    · simp only [f, if_pos h]
      exact (h.sub h0).const_smul c⁻¹
    · simp only [f, if_neg h]
      exact aestronglyMeasurable_const
  · filter_upwards [hdiff] with t ht
    have h1 := hasLineDerivAt_iff_tendsto_slope_zero.1 (ht.hasFDerivAt.hasLineDerivAt v)
    refine h1.congr' ?_
    filter_upwards [hev] with c hc
    simp only [f, if_pos hc]

variable [FiniteDimensional ℂ E]

theorem aestronglyMeasurable_fderiv_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀) μ := by
  let b := Module.finBasis ℂ E
  have key : (fun t => fderiv ℂ (F t) x₀) = fun t =>
      ∑ i, ContinuousLinearMap.smulRightL ℂ E V
        (LinearMap.toContinuousLinearMap (b.coord i)) (fderiv ℂ (F t) x₀ (b i)) := by
    funext t
    ext v
    have h : fderiv ℂ (F t) x₀ v = ∑ i, (b.repr v) i • fderiv ℂ (F t) x₀ (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul]
    simpa using h
  rw [key]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℂ E V
    (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_fderiv_apply_of_param hmeas hdiff (b i))

set_option linter.unusedSectionVars false

variable [CompleteSpace V]

theorem hasFDerivAt_integral_of_holomorphic_of_dominated {F : T → E → V} {x₀ : E} {s : Set E}
    {bound : T → ℝ} (hs : s ∈ 𝓝 x₀)
    (hmeas : ∀ y ∈ s, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) s)
    (hbound : ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) (hint : Integrable bound μ) :
    Integrable (fun t => F t x₀) μ ∧ Integrable (fun t => fderiv ℂ (F t) x₀) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  have hat : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀ := hdiff.mono fun t ht => ht.differentiableAt hs
  have hF₀ : Integrable (fun t => F t x₀) μ :=
    hint.mono' (hmeas x₀ hx₀) (hbound.mono fun t ht => ht x₀ hx₀)
  refine ⟨hF₀, ?_⟩
  refine hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℂ) (F := fun y t => F t y)
    (F' := fun t => fderiv ℂ (F t) x₀) (bound := fun t => 2 * bound t / r)
    (ball_mem_nhds x₀ hr) (fun y hy => hmeas y (hrs hy)) hF₀
    (aestronglyMeasurable_fderiv_of_param (Filter.mem_of_superset hs hmeas) hat) ?_
    ((hint.const_mul 2).div_const r) (hat.mono fun t ht => ht.hasFDerivAt)
  filter_upwards [hdiff, hbound] with t ht hb y hy
  have hmaps : MapsTo (F t) (ball x₀ r) (closedBall (F t x₀) (2 * bound t)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hb z (hrs hz)
    have h2 := hb x₀ hx₀
    linarith [norm_sub_le (F t z) (F t x₀)]
  simpa [dist_eq_norm] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball (ht.mono hrs) hmaps hy

theorem differentiableOn_integral_of_holomorphic_of_locally_dominated {F : T → E → V}
    {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) U)
    (hdom : ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ bound : T → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  have key : ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
    intro x hx
    obtain ⟨s, hs, bound, hint, hb⟩ := hdom x hx
    exact hasFDerivAt_integral_of_holomorphic_of_dominated (s := s ∩ U)
      (inter_mem hs (hU.mem_nhds hx)) (fun y hy => hmeas y hy.2)
      (hdiff.mono fun t ht => ht.mono inter_subset_right)
      (hb.mono fun t ht y hy => ht y hy.1) hint
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

theorem differentiableOn_setIntegral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] {F : T → E → V} {U : Set E} (hU : IsOpen U) {S K : Set T}
    (hK : IsCompact K) (hSK : S ⊆ K) (hS : MeasurableSet S) (hfin : μ S ≠ ⊤)
    (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ U))
    (hdiff : ∀ t ∈ S, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in S, F t y ∂μ) U ∧
      ∀ x ∈ U, IntegrableOn (fun t => F t x) S μ ∧
        IntegrableOn (fun t => fderiv ℂ (F t) x) S μ ∧
        HasFDerivAt (fun y => ∫ t in S, F t y ∂μ) (∫ t in S, fderiv ℂ (F t) x ∂μ) x := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfin.lt_top⟩
  refine differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ.restrict S) hU
    (fun y hy => ?_) (ae_restrict_of_forall_mem hS hdiff) (fun x hx => ?_)
  · have : ContinuousOn (fun t => F t y) K :=
      hcont.comp (f := fun t => (t, y)) (by fun_prop) fun t ht => ⟨ht, hy⟩
    exact this.aestronglyMeasurable_of_subset_isCompact hK hS hSK
  · obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
      (hcont.mono (prod_mono subset_rfl hrU))
    refine ⟨closedBall x r, closedBall_mem_nhds x hr, fun _ => C, integrable_const C, ?_⟩
    exact ae_restrict_of_forall_mem hS fun t ht y hy => hC (t, y) ⟨hSK ht, hy⟩

theorem differentiableOn_integral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] [CompactSpace T] [IsFiniteMeasure μ] {F : T → E → V} {U : Set E}
    (hU : IsOpen U) (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ U))
    (hdiff : ∀ t, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  simpa only [Measure.restrict_univ, integrableOn_univ] using
    differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := μ) hU isCompact_univ
      subset_rfl MeasurableSet.univ (measure_ne_top μ _) hcont fun t _ => hdiff t

theorem differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn {F : ℝ → E → V}
    {U : Set E} (hU : IsOpen U) {a b : ℝ}
    (hcont : ContinuousOn (Function.uncurry F) ([[a, b]] ×ˢ U))
    (hdiff : ∀ t ∈ [[a, b]], DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in a..b, F t y) U ∧
      ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
        IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
        HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
  have h := differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume) hU
    (isCompact_uIcc (a := a) (b := b)) uIoc_subset_uIcc measurableSet_uIoc
    (by simp [uIoc]) hcont fun t ht => hdiff t (uIoc_subset_uIcc ht)
  have key : ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
      IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
      HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := h.2 x hx
    refine ⟨intervalIntegrable_iff.2 h1, intervalIntegrable_iff.2 h2, ?_⟩
    simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    split_ifs
    · simpa using h3
    · simpa using h3.fun_neg
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

end GlobalTheory
