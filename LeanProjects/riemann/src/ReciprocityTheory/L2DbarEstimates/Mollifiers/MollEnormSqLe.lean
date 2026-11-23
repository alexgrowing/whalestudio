import ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem Kernel.lintegral_ofReal (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) :
    ∫⁻ t, ENNReal.ofReal (K.toFun t) ∂μ = 1 := by
  have hint : Integrable K.toFun μ :=
    Integrable.of_integral_ne_zero (by rw [K.integral_eq_one]; exact one_ne_zero)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall K.nonneg),
    K.integral_eq_one, ENNReal.ofReal_one]

theorem moll_enorm_sq_le (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : AEStronglyMeasurable u μ)
    (x : E) :
    ‖moll K u x‖ₑ ^ 2 ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
  have hK0 := K.nonneg
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  have h1 : ‖moll K u x‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    have hmoll : moll K u x = ∫ t, K.toFun t • u (x - t) ∂μ := rfl
    rw [hmoll]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (hK0 t)]
  have hum : AEMeasurable (fun t => ‖u (x - t)‖ₑ) μ :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)).enorm
  set f : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) with hfdef
  set g : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) * ‖u (x - t)‖ₑ with hgdef
  have hf : AEMeasurable f μ := hKm.sqrt.ennreal_ofReal.aemeasurable
  have hg : AEMeasurable g μ := hf.mul hum
  have r2 : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z ^ 2 := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have hsq : ∀ t, ENNReal.ofReal (Real.sqrt (K.toFun t)) ^ 2 = ENNReal.ofReal (K.toFun t) := by
    intro t
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hK0 t)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : ∫⁻ t, (f * g) t ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply, hfdef, hgdef]
    rw [← mul_assoc, ← pow_two, hsq]
  have e2 : ∫⁻ t, f t ^ (2 : ℝ) ∂μ = 1 := by
    rw [← Kernel.lintegral_ofReal E μ K]
    refine lintegral_congr fun t => ?_
    simp only [hfdef]
    rw [r2, hsq]
  have e3 : ∫⁻ t, g t ^ (2 : ℝ) ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [hgdef]
    rw [r2, mul_pow, hsq]
  rw [e1, e2, e3, ENNReal.one_rpow, one_mul] at hH
  calc ‖moll K u x‖ₑ ^ 2
      ≤ ((∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1.trans hH) 2
    _ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem moll_young_sq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) (u : E → ℂ) (s : Set E) (hs : MeasurableSet s)
    (hu : AEStronglyMeasurable u μ) :
    ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ ≤ ∫⁻ y in thickening K.r s, ‖u y‖ₑ ^ 2 ∂μ := by
  set T := thickening K.r s with hTdef
  have hT : MeasurableSet T := isOpen_thickening.measurableSet
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  set F : E → E → ℝ≥0∞ := fun x t => ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 with hFdef
  have hF : AEMeasurable (Function.uncurry F) ((μ.restrict s).prod μ) := by
    have hq := hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
    have hF0 : AEMeasurable (Function.uncurry F) (μ.prod μ) :=
      (hKm.comp measurable_snd).ennreal_ofReal.aemeasurable.mul (hq.enorm.pow_const 2)
    exact hF0.mono_ac (Measure.restrict_le_self.absolutelyContinuous.prod
      (Measure.AbsolutelyContinuous.refl μ))
  have htrans : ∀ t, ∫⁻ x in (fun x => x - t) ⁻¹' T, ‖u (x - t)‖ₑ ^ 2 ∂μ =
      ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    rw [← lintegral_indicator (hT.preimage (measurable_sub_const t)), ← lintegral_indicator hT,
      ← lintegral_sub_right_eq_self (T.indicator fun y => ‖u y‖ₑ ^ 2) t]
    refine lintegral_congr fun x => ?_
    first
    | rfl
    | (by_cases hx : x - t ∈ T <;> simp [Set.indicator_apply, hx])
  have hpt : ∀ t, ∫⁻ x in s, F x t ∂μ ≤ ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    simp only [hFdef]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    by_cases h0 : K.toFun t = 0
    · simp [h0]
    · have ht : t ∈ ball (0 : E) K.r := K.support_subset h0
      refine mul_le_mul' le_rfl ?_
      rw [← htrans t]
      refine lintegral_mono_set fun x hx => ?_
      simp only [Set.mem_preimage, hTdef]
      refine mem_thickening_iff.mpr ⟨x, hx, ?_⟩
      rw [mem_ball_zero_iff] at ht
      simpa [dist_eq_norm] using ht
  calc ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in s, ∫⁻ t, F x t ∂μ ∂μ :=
        lintegral_mono fun x => moll_enorm_sq_le E μ K hu x
    _ = ∫⁻ t, ∫⁻ x in s, F x t ∂μ ∂μ := lintegral_lintegral_swap hF
    _ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ ∂μ := lintegral_mono hpt
    _ = ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
        rw [lintegral_mul_const _ hKm.ennreal_ofReal, Kernel.lintegral_ofReal E μ K, one_mul]

theorem moll_young (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : YoungSt E μ := by
  intro K u s hs hu
  have h := moll_young_sq E μ K u s hs hu
  have e : ∀ z : ℝ≥0∞, z ^ (ENNReal.toReal 2) = z ^ 2 := fun z => by
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]; norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp_rw [e]
  exact ENNReal.rpow_le_rpow h (by norm_num)

theorem mollifier_memL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : MollifierMemL2 E μ := by
  intro K u hu
  have hT : thickening K.r (univ : Set E) = univ :=
    eq_univ_of_forall fun x => mem_thickening_iff.mpr ⟨x, mem_univ _, by simpa using K.r_pos⟩
  have hY := moll_young E μ K u univ MeasurableSet.univ hu.1
  rw [hT, Measure.restrict_univ] at hY
  have hcs : HasCompactSupport K.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall (K.support_subset h))
  have hc : Continuous (moll K u) :=
    hcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) K.smooth.continuous
      (hu.locallyIntegrable (by norm_num))
  exact ⟨⟨hc.aestronglyMeasurable, hY.trans_lt hu.2⟩, hY⟩

end ReciprocityTheory.L2DbarEstimates.B
