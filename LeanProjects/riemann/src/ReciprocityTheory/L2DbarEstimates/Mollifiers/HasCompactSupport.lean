import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

theorem Kernel.hasCompactSupport (K : Kernel E μ) : HasCompactSupport K.toFun :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun x hx => by
    by_contra h
    exact hx (ball_subset_closedBall (K.support_subset h))

theorem Kernel.eq_zero_of_le (K : Kernel E μ) {t : E} (ht : K.r ≤ ‖t‖) : K.toFun t = 0 := by
  by_contra h
  have h' := K.support_subset h
  rw [mem_ball_zero_iff] at h'
  linarith

theorem moll_apply (K : Kernel E μ) (u : E → ℂ) (x : E) :
    moll K u x = ∫ t, K.toFun t • u (x - t) ∂μ := rfl

end

theorem moll_apply_swap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) (u : E → ℂ) (x : E) :
    moll K u x = ∫ y, K.toFun (x - y) • u y ∂μ := by
  rw [moll, convolution_eq_swap]
  rfl

theorem moll_smooth (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothSt E μ := fun K _ hu =>
  K.hasCompactSupport.contDiff_convolution_left _ K.smooth hu

theorem moll_support (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SupportSt E μ := by
  intro K u
  refine (support_convolution_subset _).trans ?_
  rw [add_comm]
  exact Set.add_subset_add_left K.support_subset

theorem moll_compact (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : CompactSt E μ := fun K _ hu =>
  K.hasCompactSupport.convolution _ hu

theorem moll_congr (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : CongrSt E μ := fun _ _ _ h =>
  convolution_congr _ EventuallyEq.rfl h

theorem moll_local (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : LocalSt E μ := by
  intro K u s x hs
  rw [moll_apply, moll_apply]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : K.toFun t = 0
  · simp [ht]
  have htr := K.support_subset ht
  rw [mem_ball_zero_iff] at htr
  have hxt : x - t ∈ s := hs (by rw [mem_ball, dist_eq_norm]; simpa using htr)
  simp [Set.indicator_of_mem hxt]

theorem moll_sub (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u u' : E → ℂ} (hu : LocallyIntegrable u μ)
    (hu' : LocallyIntegrable u' μ) : moll K (u - u') = moll K u - moll K u' := by
  funext x
  have h1 := K.hasCompactSupport.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    K.smooth.continuous hu x
  have h2 := K.hasCompactSupport.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    K.smooth.continuous hu' x
  simp only [Pi.sub_apply, moll_apply, smul_sub]
  exact integral_sub h1 h2

theorem kernel_std (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : StdSt E μ := by
  have h : (fun ε : ℝ => (Kernel.std E μ ε).r) =ᶠ[𝓝[>] 0] id := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [Kernel.std, Kernel.ofBump, stdBump, show (0 : ℝ) < ε from hε]
  exact (tendsto_congr' h).2 (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)

end ReciprocityTheory.L2DbarEstimates.B
