import ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem fderiv_moll_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : LocallyIntegrable u μ)
    (x a : E) :
    fderiv ℝ (moll K u) x a = ∫ y, (fderiv ℝ K.toFun (x - y) a) • u y ∂μ := by
  have hcs : HasCompactSupport K.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun y hy => by
      by_contra h
      exact hy (ball_subset_closedBall (K.support_subset h))
  have hd := hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (K.smooth.of_le (by simp)) hu x
  have hmoll : moll K u = K.toFun ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u := rfl
  rw [hmoll, hd.fderiv]
  have hex := (hcs.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (K.smooth.continuous_fderiv (by simp)) hu x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  rw [← integral_sub_left_eq_self _ μ x]
  congr 1
  ext y
  rw [sub_sub_cancel]
  rfl

theorem moll_weakComm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : WeakCommSt E μ := by
  intro m c v g w hw K
  funext x
  have hd : ∀ k, fderiv ℝ (moll K (g k)) x (v k) =
      ∫ y, (fderiv ℝ K.toFun (x - y) (v k)) • g k y ∂μ :=
    fun k => fderiv_moll_apply E μ K (hw.1 k) x (v k)
  set φ : E → ℂ := fun y => ((K.toFun (x - y) : ℝ) : ℂ) with hφdef
  have hφs : ContDiff ℝ ∞ φ :=
    Complex.ofRealCLM.contDiff.comp (K.smooth.comp (contDiff_const.sub contDiff_id))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall x K.r) fun y hy => by
      simp only [hφdef, Complex.ofReal_eq_zero]
      by_contra h
      apply hy
      have h' := K.support_subset h
      rw [mem_ball_zero_iff] at h'
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact h'.le
  have hw3 := hw.2.2 φ hφs hφc
  have hdφ : ∀ y a, fderiv ℝ φ y a = -((fderiv ℝ K.toFun (x - y) a : ℝ) : ℂ) := by
    intro y a
    have h1 : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((K.smooth.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    rw [(show HasFDerivAt φ _ y from h3).fderiv]
    simp
  have hm : moll K w x = ∫ y, w y * φ y ∂μ := by
    show ∫ t, K.toFun t • w (x - t) ∂μ = _
    rw [← integral_sub_left_eq_self (fun t => K.toFun t • w (x - t)) μ x]
    congr 1
    ext y
    simp only [hφdef, sub_sub_cancel, Complex.real_smul]
    ring
  simp only [Dop, hd]
  rw [hm, hw3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_neg, ← integral_neg]
  congr 2
  ext y
  rw [hdφ, Complex.real_smul]
  ring

theorem smooth_isWeakD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothWeakSt E μ := by
  intro m c v g hg
  have hgd : ∀ k, Differentiable ℝ (g k) := fun k => (hg k).differentiable (by simp)
  have hgc : ∀ k, Continuous (fun x => fderiv ℝ (g k) x (v k)) := fun k =>
    ((hg k).continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun k => (hg k).continuous.locallyIntegrable, ?_, ?_⟩
  · have hc : Continuous (Dop c v g) := by
      unfold Dop
      exact continuous_finset_sum _ fun k _ => continuous_const.mul (hgc k)
    exact hc.locallyIntegrable
  · intro φ hφ hφc
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hφ' : ∀ k, Continuous (fun x => fderiv ℝ φ x (v k)) := fun k =>
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφ'c : ∀ k, HasCompactSupport (fun x => fderiv ℝ φ x (v k)) := fun k =>
      (hφc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℂ => L (v k)) (by simp)
    have int1 : ∀ k, Integrable (fun x => fderiv ℝ (g k) x (v k) * φ x) μ := fun k =>
      ((hgc k).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have int2 : ∀ k, Integrable (fun x => g k x * fderiv ℝ φ x (v k)) μ := fun k =>
      ((hg k).continuous.mul (hφ' k)).integrable_of_hasCompactSupport (hφ'c k).mul_left
    have int3 : ∀ k, Integrable (fun x => g k x * φ x) μ := fun k =>
      ((hg k).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have hibp : ∀ k, ∫ x, g k x * fderiv ℝ φ x (v k) ∂μ =
        -∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ := fun k =>
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (int1 k) (int2 k) (int3 k)
        (fun x _ => hgd k x) (fun x _ => hφd x)
    have hsum : ∫ x, Dop c v g x * φ x ∂μ =
        ∑ k, c k * ∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ := by
      simp only [Dop, Finset.sum_mul]
      rw [integral_finset_sum _ fun k _ => by simpa [mul_assoc] using (int1 k).const_mul (c k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_const_mul]
      congr 1
      ext x
      ring
    rw [hsum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hibp k, mul_neg, neg_neg]

end ReciprocityTheory.L2DbarEstimates.B
