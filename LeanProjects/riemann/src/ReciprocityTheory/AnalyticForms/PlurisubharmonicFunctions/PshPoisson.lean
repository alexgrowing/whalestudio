import Mathlib

open Complex Metric Real Filter Topology InnerProductSpace

namespace ReciprocityTheory.AnForm.A

noncomputable def poissonInt (g : ℂ → ℝ) (r : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 w • g) 0 r

private lemma sub_ne_zero_of_mem_sphere_of_mem_ball {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : z - w ≠ 0 := by
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  intro h
  rw [sub_eq_zero] at h
  rw [h] at hz
  linarith

private lemma re_herglotzRieszKernel_eq_poissonKernel (w z : ℂ) :
    (herglotzRieszKernel 0 w z).re = poissonKernel 0 w z := by
  rw [herglotzRieszKernel_def, poissonKernel_def]
  first
  | (simp only [sub_zero, Complex.div_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]; ring)
  | (simp only [sub_zero, Complex.div_re, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]; ring)

lemma poissonKernel_zero_continuousOn {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 r) := by
  have hfun : poissonKernel 0 w = fun z ↦ (‖z - 0‖ ^ 2 - ‖w - 0‖ ^ 2) / ‖z - 0 - (w - 0)‖ ^ 2 :=
    funext (poissonKernel_def 0 w)
  rw [hfun]
  refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
    (Continuous.continuousOn (by fun_prop)) ?_
  intro z hz
  have h := sub_ne_zero_of_mem_sphere_of_mem_ball hw hz
  simp only [sub_zero]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h)

lemma poissonKernel_zero_nonneg {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : 0 ≤ poissonKernel 0 w z := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  refine div_nonneg ?_ (sq_nonneg _)
  simp only [sub_zero]
  rw [hz]
  nlinarith [norm_nonneg w]

lemma poissonKernel_zero_le {r δ : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) (hδ : 0 < δ) (hzw : δ ≤ ‖z - w‖) :
    poissonKernel 0 w z ≤ (r ^ 2 - ‖w‖ ^ 2) / δ ^ 2 := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  simp only [sub_zero]
  rw [hz]
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hden : δ ^ 2 ≤ ‖z - w‖ ^ 2 := by nlinarith [hzw, hδ]
  first
  | exact div_le_div_of_nonneg_left hnum (pow_pos hδ 2) hden
  | exact div_le_div_of_le_left hnum (pow_pos hδ 2) hden
  | (gcongr; all_goals first | exact hnum | exact hδ.le | exact hzw | exact pow_pos hδ 2)

lemma circleAverage_poissonKernel_zero {r : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    Real.circleAverage (poissonKernel 0 w) 0 r = 1 := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg w) (mem_ball_zero_iff.mp hw)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hD : deriv (circleMap (0 : ℂ) r) = fun θ ↦ circleMap 0 r θ * I :=
    funext (deriv_circleMap 0 r)
  have hc : Continuous (circleMap (0 : ℂ) r) := continuous_circleMap 0 r
  have hAs : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ ↦ circleMap_mem_sphere 0 hr.le θ
  have hAw : ∀ θ : ℝ, circleMap 0 r θ - w ≠ 0 := fun θ ↦ sub_ne_zero_of_mem_sphere_of_mem_ball hw (hAs θ)
  have hA0 : ∀ θ : ℝ, circleMap 0 r θ - 0 ≠ 0 := fun θ ↦ sub_ne_zero_of_mem_sphere_of_mem_ball h0 (hAs θ)
  have hc1 : Continuous (fun θ : ℝ ↦ deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹) := by
    rw [hD]; exact (hc.mul continuous_const).smul ((hc.sub continuous_const).inv₀ hAw)
  have hc2 : Continuous (fun θ : ℝ ↦ deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹) := by
    rw [hD]; exact (hc.mul continuous_const).smul ((hc.sub continuous_const).inv₀ hA0)
  have hi1 : IntervalIntegrable
      (fun θ : ℝ ↦ (2 : ℂ) * (deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹))
      MeasureTheory.volume 0 (2 * π) := (continuous_const.mul hc1).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)
      MeasureTheory.volume 0 (2 * π) := hc2.intervalIntegrable _ _
  have hGint : IntervalIntegrable
      (fun θ : ℝ ↦ -I * ((2 : ℂ) * (deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹) -
        deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹))
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul ((continuous_const.mul hc1).sub hc2)).intervalIntegrable _ _
  have hI1 := circleIntegral.integral_sub_inv_of_mem_ball hw
  have hI2 := circleIntegral.integral_sub_inv_of_mem_ball h0
  simp only [circleIntegral] at hI1 hI2
  have hGi : ∫ θ in (0 : ℝ)..2 * π, -I * ((2 : ℂ) * (deriv (circleMap 0 r) θ •
      (circleMap 0 r θ - w)⁻¹) - deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹) =
      ((2 * π : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul, hI1, hI2]
    push_cast
    linear_combination (-2 * (π : ℂ)) * Complex.I_mul_I
  have hpt : ∀ θ : ℝ, poissonKernel 0 w (circleMap 0 r θ) =
      (-I * ((2 : ℂ) * (deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹) -
        deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)).re := by
    intro θ
    rw [← re_herglotzRieszKernel_eq_poissonKernel, herglotzRieszKernel_def, deriv_circleMap]
    congr 1
    have h1 := hAw θ
    have h2 := hA0 θ
    simp only [sub_zero, smul_eq_mul] at h2 ⊢
    have hII : -I * I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    calc (circleMap 0 r θ + w) / (circleMap 0 r θ - w)
        = circleMap 0 r θ * (2 * (circleMap 0 r θ - w)⁻¹ - (circleMap 0 r θ)⁻¹) := by
          field_simp <;> ring
      _ = (-I * I) * (circleMap 0 r θ * (2 * (circleMap 0 r θ - w)⁻¹ - (circleMap 0 r θ)⁻¹)) := by
          rw [hII, one_mul]
      _ = -I * (2 * (circleMap 0 r θ * I * (circleMap 0 r θ - w)⁻¹) -
            circleMap 0 r θ * I * (circleMap 0 r θ)⁻¹) := by ring
  have hre : ∫ θ in (0 : ℝ)..2 * π, (-I * ((2 : ℂ) * (deriv (circleMap 0 r) θ •
      (circleMap 0 r θ - w)⁻¹) - deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)).re =
      (∫ θ in (0 : ℝ)..2 * π, -I * ((2 : ℂ) * (deriv (circleMap 0 r) θ •
      (circleMap 0 r θ - w)⁻¹) - deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)).re := by
    first
    | exact Complex.reCLM.intervalIntegral_comp_comm hGint
    | exact intervalIntegral.integral_re hGint
  unfold Real.circleAverage
  rw [intervalIntegral.integral_congr (fun θ _ ↦ hpt θ), hre, hGi, Complex.ofReal_re, smul_eq_mul]
  exact inv_mul_cancel₀ (by positivity)

lemma poissonInt_eq_re {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poissonInt g r w =
      (Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 r).re := by
  have hH : ContinuousOn (herglotzRieszKernel 0 w) (sphere 0 r) := by
    rw [show herglotzRieszKernel 0 w = fun ζ ↦ (ζ - 0 + (w - 0)) / (ζ - 0 - (w - 0)) from
      funext (herglotzRieszKernel_def 0 w)]
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) ?_
    intro z hz
    simpa using sub_ne_zero_of_mem_sphere_of_mem_ball hw hz
  have hgc : ContinuousOn (fun ζ ↦ (g ζ : ℂ)) (sphere 0 r) :=
    Complex.continuous_ofReal.comp_continuousOn hg
  have hi : CircleIntegrable (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 r :=
    (hH.smul hgc).circleIntegrable hr.le
  have hre : ∫ θ in (0 : ℝ)..2 * π,
      (herglotzRieszKernel 0 w (circleMap 0 r θ) • (g (circleMap 0 r θ) : ℂ)).re =
      (∫ θ in (0 : ℝ)..2 * π,
        herglotzRieszKernel 0 w (circleMap 0 r θ) • (g (circleMap 0 r θ) : ℂ)).re := by
    first
    | exact Complex.reCLM.intervalIntegral_comp_comm hi
    | exact intervalIntegral.integral_re hi
  unfold poissonInt Real.circleAverage
  rw [Complex.smul_re, ← hre]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, re_herglotzRieszKernel_eq_poissonKernel]

private lemma poissonInt_eq_re_cauchy_integral {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poissonInt g r w = (2 * ((2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r), (z - w)⁻¹ • ((g z : ℝ) : ℂ)) -
      ((Real.circleAverage g 0 r : ℝ) : ℂ)).re := by
  rw [poissonInt_eq_re hr hg hw]
  congr 1
  have hc : Continuous (circleMap (0 : ℂ) r) := continuous_circleMap 0 r
  have hAs : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ ↦ circleMap_mem_sphere 0 hr.le θ
  have hAw : ∀ θ : ℝ, circleMap 0 r θ - w ≠ 0 := fun θ ↦ sub_ne_zero_of_mem_sphere_of_mem_ball hw (hAs θ)
  have hgA : Continuous (fun θ : ℝ ↦ ((g (circleMap 0 r θ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hg.comp_continuous hc hAs)
  have hD : deriv (circleMap (0 : ℂ) r) = fun θ ↦ circleMap 0 r θ * I :=
    funext (deriv_circleMap 0 r)
  have hc1 : Continuous (fun θ : ℝ ↦ deriv (circleMap 0 r) θ •
      ((circleMap 0 r θ - w)⁻¹ • ((g (circleMap 0 r θ) : ℝ) : ℂ))) := by
    rw [hD]
    exact (hc.mul continuous_const).smul (((hc.sub continuous_const).inv₀ hAw).smul hgA)
  have hi1 : IntervalIntegrable (fun θ : ℝ ↦ -((g (circleMap 0 r θ) : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * π) := hgA.neg.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ ↦ (2 * -I) * (deriv (circleMap 0 r) θ •
      ((circleMap 0 r θ - w)⁻¹ • ((g (circleMap 0 r θ) : ℝ) : ℂ))))
      MeasureTheory.volume 0 (2 * π) := (continuous_const.mul hc1).intervalIntegrable _ _
  have hpt : ∀ θ : ℝ, herglotzRieszKernel 0 w (circleMap 0 r θ) • ((g (circleMap 0 r θ) : ℝ) : ℂ) =
      -((g (circleMap 0 r θ) : ℝ) : ℂ) + (2 * -I) * (deriv (circleMap 0 r) θ •
        ((circleMap 0 r θ - w)⁻¹ • ((g (circleMap 0 r θ) : ℝ) : ℂ))) := by
    intro θ
    have h1 := hAw θ
    have e : ∀ X : ℂ, (2 * -I) * (circleMap 0 r θ * I * X) = 2 * circleMap 0 r θ * X := by
      intro X
      linear_combination (-2 * circleMap 0 r θ * X) * Complex.I_mul_I
    rw [herglotzRieszKernel_def, deriv_circleMap]
    simp only [sub_zero, smul_eq_mul]
    rw [e]
    field_simp <;> ring
  unfold Real.circleAverage
  simp only [circleIntegral]
  rw [intervalIntegral.integral_congr (fun θ _ ↦ hpt θ), intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  rw [mul_inv (2 * (π : ℂ)) I, Complex.inv_I]
  ring

lemma poissonInt_harmonicAt {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) : HarmonicAt (poissonInt g r) w := by
  have hgc : ContinuousOn (fun ζ ↦ ((g ζ : ℝ) : ℂ)) (sphere 0 r) :=
    Complex.continuous_ofReal.comp_continuousOn hg
  have hps := hasFPowerSeriesOn_cauchy_integral
    (hgc.circleIntegrable hr.le :
      CircleIntegrable (fun ζ ↦ ((g ζ : ℝ) : ℂ)) 0 ((⟨r, hr.le⟩ : NNReal) : ℝ))
    (NNReal.coe_pos.mp hr)
  have hCa : AnalyticAt ℂ
      (fun w' ↦ (2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r), (z - w')⁻¹ • ((g z : ℝ) : ℂ)) w := by
    refine hps.analyticAt_of_mem ?_
    first
    | (rw [Metric.emetric_ball_nnreal]; exact hw)
    | simpa [Metric.emetric_ball_nnreal] using hw
    | (refine EMetric.mem_ball.mpr (edist_lt_coe.mpr (NNReal.coe_lt_coe.mp ?_))
       rw [coe_nndist, dist_zero_right]
       exact mem_ball_zero_iff.mp hw)
    | (have hw' : ‖w‖ < r := mem_ball_zero_iff.mp hw
       simp only [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
       exact NNReal.coe_lt_coe.mp hw')
  have hFa : AnalyticAt ℂ (fun w' ↦ 2 * ((2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r),
      (z - w')⁻¹ • ((g z : ℝ) : ℂ)) - ((Real.circleAverage g 0 r : ℝ) : ℂ)) w :=
    (analyticAt_const.mul hCa).sub analyticAt_const
  have hev : poissonInt g r =ᶠ[𝓝 w] fun w' ↦ (2 * ((2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r),
      (z - w')⁻¹ • ((g z : ℝ) : ℂ)) - ((Real.circleAverage g 0 r : ℝ) : ℂ)).re := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
    exact poissonInt_eq_re_cauchy_integral hr hg hw'
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr hFa.harmonicAt_re

lemma poissonInt_zero {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) :
    poissonInt g r 0 = Real.circleAverage g 0 r := by
  unfold poissonInt
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hz
  have hz0 : ‖z‖ ≠ 0 := by rw [hz]; exact hr.ne'
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, poissonKernel_def, sub_zero, norm_zero]
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hz0)]
  ring

lemma poissonInt_sub {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) (c : ℝ) :
    poissonInt g r w - c =
      Real.circleAverage (fun z ↦ poissonKernel 0 w z * (g z - c)) 0 r := by
  have hP : CircleIntegrable (poissonKernel 0 w) 0 r :=
    (poissonKernel_zero_continuousOn hr hw).circleIntegrable hr.le
  have hPg : IntervalIntegrable
      (fun θ : ℝ ↦ poissonKernel 0 w (circleMap 0 r θ) * g (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) :=
    ((poissonKernel_zero_continuousOn hr hw).mul hg).circleIntegrable hr.le
  have hPc : IntervalIntegrable (fun θ : ℝ ↦ c * poissonKernel 0 w (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) := IntervalIntegrable.const_mul hP c
  have h1 := circleAverage_poissonKernel_zero (r := r) hw
  unfold Real.circleAverage at h1
  unfold poissonInt Real.circleAverage
  have hI : (∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) * (g (circleMap 0 r θ) - c)) =
      (∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) * g (circleMap 0 r θ)) -
        c * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hPg hPc]
    congr 1
    funext θ
    ring
  simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
  rw [hI]
  linear_combination c * h1

lemma poissonInt_tendsto {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere (0 : ℂ) r) :
    Tendsto (poissonInt g r) (𝓝[ball 0 r] ζ₀) (𝓝 (g ζ₀)) := by
  have hζ : ‖ζ₀‖ = r := mem_sphere_zero_iff_norm.mp hζ₀
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M :=
    (isCompact_sphere 0 r).exists_bound_of_continuousOn (hg.sub continuousOn_const)
  obtain ⟨M', hM'⟩ : ∃ M', M' = max M 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M' := by rw [hM']; exact le_max_right _ _
  have hMM : ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M' := by
    intro z hz
    rw [hM']
    exact (hM z hz).trans (le_max_left _ _)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hgη⟩ := Metric.continuousOn_iff.mp hg ζ₀ hζ₀ (ε / 2) (half_pos hε)
  have hq : 0 < (η / 2) ^ 2 := pow_pos (half_pos hη) 2
  have hden : 0 < 8 * r * (M' + 1) := mul_pos (mul_pos (by norm_num) hr) (by linarith)
  refine ⟨min (η / 2) (ε * (η / 2) ^ 2 / (8 * r * (M' + 1))),
    lt_min (half_pos hη) (div_pos (mul_pos hε hq) hden), ?_⟩
  intro w hw hwd
  have hwb : ‖w‖ < r := mem_ball_zero_iff.mp hw
  have hδ1 : dist w ζ₀ < η / 2 := lt_of_lt_of_le hwd (min_le_left _ _)
  have hδ2 : dist w ζ₀ < ε * (η / 2) ^ 2 / (8 * r * (M' + 1)) :=
    lt_of_lt_of_le hwd (min_le_right _ _)
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  obtain ⟨K, hK⟩ : ∃ K, K = M' * ((r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg hM0 (div_nonneg hnum hq.le)
  have hd : r - ‖w‖ ≤ dist w ζ₀ := by
    rw [dist_comm, dist_eq_norm, ← hζ]
    exact norm_sub_norm_le ζ₀ w
  have hnum2 : r ^ 2 - ‖w‖ ^ 2 ≤ 2 * r * dist w ζ₀ := by
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * r),
      sq_nonneg (r - ‖w‖), norm_nonneg w]
  have hd2 : dist w ζ₀ * (8 * r * (M' + 1)) < ε * (η / 2) ^ 2 := by
    first
    | exact (lt_div_iff₀ hden).mp hδ2
    | exact (lt_div_iff hden).mp hδ2
  have hKq : K * (η / 2) ^ 2 = M' * (r ^ 2 - ‖w‖ ^ 2) := by
    rw [hK, mul_assoc, div_mul_cancel₀ _ hq.ne']
  have hKlt : K < ε / 2 := by
    have h1 : M' * (r ^ 2 - ‖w‖ ^ 2) ≤ (M' + 1) * (2 * r * dist w ζ₀) := by
      have e1 := mul_le_mul_of_nonneg_left hnum2 hM0
      have e2 : 0 ≤ 2 * r * dist w ζ₀ := by positivity
      nlinarith [e1, e2]
    have h2 : K * (η / 2) ^ 2 < ε / 2 * (η / 2) ^ 2 := by
      calc K * (η / 2) ^ 2 = M' * (r ^ 2 - ‖w‖ ^ 2) := hKq
        _ ≤ (M' + 1) * (2 * r * dist w ζ₀) := h1
        _ = dist w ζ₀ * (8 * r * (M' + 1)) / 4 := by ring
        _ < ε * (η / 2) ^ 2 / 4 := by linarith
        _ ≤ ε / 2 * (η / 2) ^ 2 := by nlinarith [mul_pos hε hq]
    exact lt_of_mul_lt_mul_right h2 hq.le
  have hpt : ∀ z ∈ sphere (0 : ℂ) r,
      ‖poissonKernel 0 w z * (g z - g ζ₀)‖ ≤ ε / 2 * poissonKernel 0 w z + K := by
    intro z hz
    have hP0 := poissonKernel_zero_nonneg hw hz
    rw [norm_mul, Real.norm_of_nonneg hP0]
    by_cases hzη : dist z ζ₀ < η
    · have h3 := hgη z hz hzη
      rw [dist_eq_norm] at h3
      have h4 := mul_le_mul_of_nonneg_left h3.le hP0
      linarith
    · push_neg at hzη
      have hzw : η / 2 ≤ ‖z - w‖ := by
        have h5 := dist_triangle z w ζ₀
        rw [dist_eq_norm z w] at h5
        linarith
      have hPle := poissonKernel_zero_le hw hz (half_pos hη) hzw
      have hgM := hMM z hz
      have h6 : poissonKernel 0 w z * ‖g z - g ζ₀‖ ≤
          (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' :=
        mul_le_mul hPle hgM (norm_nonneg _) (div_nonneg hnum hq.le)
      have h7 : (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' = K := by rw [hK]; ring
      have h8 : 0 ≤ ε / 2 * poissonKernel 0 w z := mul_nonneg (half_pos hε).le hP0
      linarith
  have hPi : IntervalIntegrable (fun θ : ℝ ↦ poissonKernel 0 w (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) :=
    (poissonKernel_zero_continuousOn hr hw).circleIntegrable hr.le
  have hPint : ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) = 2 * π := by
    have h1 := circleAverage_poissonKernel_zero (r := r) hw
    unfold Real.circleAverage at h1
    rw [smul_eq_mul] at h1
    calc ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ)
        = (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ = 2 * π := by rw [h1, mul_one]
  have hbound : ‖∫ θ in (0 : ℝ)..2 * π,
      poissonKernel 0 w (circleMap 0 r θ) * (g (circleMap 0 r θ) - g ζ₀)‖ ≤
      ∫ θ in (0 : ℝ)..2 * π, (ε / 2 * poissonKernel 0 w (circleMap 0 r θ) + K) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by positivity) ?_ ?_
    · first
      | exact Filter.Eventually.of_forall (fun θ _ ↦ hpt _ (circleMap_mem_sphere 0 hr.le θ))
      | exact Filter.eventually_of_forall (fun θ _ ↦ hpt _ (circleMap_mem_sphere 0 hr.le θ))
    · exact (IntervalIntegrable.const_mul hPi (ε / 2)).add intervalIntegrable_const
  have hint : ∫ θ in (0 : ℝ)..2 * π, (ε / 2 * poissonKernel 0 w (circleMap 0 r θ) + K) =
      ε / 2 * (2 * π) + K * (2 * π) := by
    rw [intervalIntegral.integral_add (IntervalIntegrable.const_mul hPi (ε / 2))
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, hPint, sub_zero, smul_eq_mul]
    ring
  have hfin : (2 * π)⁻¹ * (ε / 2 * (2 * π) + K * (2 * π)) = ε / 2 + K := by
    field_simp <;> ring
  rw [Real.dist_eq, poissonInt_sub hr hg hw (g ζ₀)]
  unfold Real.circleAverage
  simp only [smul_eq_mul]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), ← Real.norm_eq_abs]
  calc _ ≤ (2 * π)⁻¹ * (ε / 2 * (2 * π) + K * (2 * π)) :=
        mul_le_mul_of_nonneg_left (hbound.trans_eq hint) (by positivity)
    _ = ε / 2 + K := hfin
    _ < ε := by linarith

theorem poisson_ext {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (Metric.sphere 0 r)) :
    ∃ Φ : ℂ → ℝ, ContinuousOn Φ (Metric.closedBall 0 r) ∧ (∀ ζ ∈ Metric.sphere 0 r, Φ ζ = g ζ) ∧
      Φ 0 = Real.circleAverage g 0 r ∧
      ∀ a s, 0 < s → Metric.closedBall a s ⊆ Metric.ball 0 r → Real.circleAverage Φ a s = Φ a := by
  refine ⟨fun z ↦ if ‖z‖ < r then poissonInt g r z else g z, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz) with hlt | heq
    · have hzb : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hlt
      have hca : ContinuousAt (poissonInt g r) z := by
        first
        | exact (poissonInt_harmonicAt hr hg hzb).1.continuousAt
        | exact (poissonInt_harmonicAt hr hg hzb).contDiffAt.continuousAt
      have hev : poissonInt g r =ᶠ[𝓝 z] fun z ↦ if ‖z‖ < r then poissonInt g r z else g z := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      first
      | exact (hca.congr hev).continuousWithinAt
      | exact (hca.congr_of_eventuallyEq hev.symm).continuousWithinAt
    · have hzs : z ∈ sphere (0 : ℂ) r := mem_sphere_zero_iff_norm.mpr heq
      have hval : (if ‖z‖ < r then poissonInt g r z else g z) = g z :=
        if_neg (by rw [heq]; exact lt_irrefl r)
      show Filter.Tendsto (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z)
        (𝓝[closedBall 0 r] z) (𝓝 (if ‖z‖ < r then poissonInt g r z else g z))
      rw [hval, ← Metric.ball_union_sphere, nhdsWithin_union]
      refine Filter.Tendsto.sup ?_ ?_
      · refine Filter.Tendsto.congr' ?_ (poissonInt_tendsto hr hg hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_pos (mem_ball_zero_iff.mp hy)]
      · refine Filter.Tendsto.congr' ?_ (hg z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_neg (by rw [mem_sphere_zero_iff_norm.mp hy]; exact lt_irrefl r)]
  · intro ζ hζ
    exact if_neg (by rw [mem_sphere_zero_iff_norm.mp hζ]; exact lt_irrefl r)
  · show (if ‖(0 : ℂ)‖ < r then poissonInt g r 0 else g 0) = Real.circleAverage g 0 r
    rw [if_pos (by rw [norm_zero]; exact hr)]
    exact poissonInt_zero hr
  · intro a s hs hsub
    have hev : Set.EqOn (fun z ↦ if ‖z‖ < r then poissonInt g r z else g z) (poissonInt g r)
        (sphere a |s|) := by
      intro y hy
      rw [abs_of_pos hs] at hy
      have hyb : y ∈ ball (0 : ℂ) r := hsub (sphere_subset_closedBall hy)
      exact if_pos (mem_ball_zero_iff.mp hyb)
    rw [Real.circleAverage_congr_sphere hev]
    have ha : a ∈ ball (0 : ℂ) r := hsub (mem_closedBall_self hs.le)
    show _ = (if ‖a‖ < r then poissonInt g r a else g a)
    rw [if_pos (mem_ball_zero_iff.mp ha)]
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    intro y hy
    rw [abs_of_pos hs] at hy
    exact poissonInt_harmonicAt hr hg (hsub hy)

end ReciprocityTheory.AnForm.A
