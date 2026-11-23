import Mathlib

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Filter Topology

open Set

theorem pgds_cont_polar_symm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p; simp [Complex.polarCoord_symm_apply]
  rw [this]; fun_prop

theorem pgds_integral_ball_polar {r : ℝ} (F : ℂ → ℝ) (hF : ContinuousOn F (Metric.closedBall 0 r)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
        (Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi) ∧
    ∫ z in Metric.ball (0 : ℂ) r, F z =
      ∫ s in Ioo 0 r, ∫ θ in Ioo (-Real.pi) Real.pi, s * F (Complex.polarCoord.symm (s, θ)) := by
  have hc := pgds_cont_polar_symm
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p))
      (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply ContinuousOn.mul (continuous_fst.continuousOn)
    refine hF.comp hc.continuousOn ?_
    intro p hp
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
    rw [abs_of_nonneg hp.1.1]; exact hp.1.2
  have hint' := hint.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  refine ⟨hint', ?_⟩
  have hpre : MeasurableSet ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) :=
    hc.measurable Metric.isOpen_ball.measurableSet
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, ← Complex.integral_comp_polarCoord_symm,
    polarCoord_target]
  have h1 : (fun p : ℝ × ℝ => p.1 • (Metric.ball (0:ℂ) r).indicator F (Complex.polarCoord.symm p)) =
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r).indicator
        (fun p : ℝ × ℝ => p.1 * F (Complex.polarCoord.symm p)) := by
    funext p
    by_cases hp : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ _ from hp), smul_eq_mul]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ _ from hp), smul_zero]
  rw [h1, setIntegral_indicator hpre]
  have h2 : Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi ∩
      ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball 0 r) =
      Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_preimage, Metric.mem_ball,
      dist_zero_right, Complex.norm_polarCoord_symm]
    constructor
    · rintro ⟨⟨h0, hθ⟩, hr⟩; rw [abs_of_pos h0] at hr; exact ⟨⟨h0, hr⟩, hθ⟩
    · rintro ⟨⟨h0, hr⟩, hθ⟩; refine ⟨⟨h0, hθ⟩, ?_⟩; rw [abs_of_pos h0]; exact hr
  rw [h2, Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at hint'
  exact setIntegral_prod _ hint'

def discI (a R : ℝ) : ℝ :=
  ∫ z in Metric.ball (0 : ℂ) R, Real.exp (-(a * ‖z‖ ^ 2))

theorem pgds_discI_eq (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    discI a R = ∫ s in (0:ℝ)..R, 2 * Real.pi * (s * Real.exp (-(a * s ^ 2))) := by
  unfold discI
  rw [(pgds_integral_ball_polar (r := R) (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2)))
    (by fun_prop)).2, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
  simp only [Complex.norm_polarCoord_symm]
  rw [abs_of_pos hs.1, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

theorem discI_of_pos {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    discI a R = Real.pi * (1 - Real.exp (-(a * R ^ 2))) / a := by
  rw [pgds_discI_eq a hR]
  have hd : ∀ x ∈ uIcc 0 R, HasDerivAt (fun s => -(Real.pi / a) * Real.exp (-(a * s ^ 2)))
      (2 * Real.pi * (x * Real.exp (-(a * x ^ 2)))) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).const_mul a).neg.exp).const_mul (-(Real.pi / a))
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    simp only [Pi.neg_apply, Nat.cast_ofNat]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
    Real.exp_zero, mul_one]
  ring

theorem discI_zero {R : ℝ} (hR : 0 ≤ R) : discI 0 R = Real.pi * R ^ 2 := by
  rw [pgds_discI_eq 0 hR]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

theorem discI_pos {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) : 0 < discI a R := by
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos ha hR.le]
    have : Real.exp (-(a * R ^ 2)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hR])
    have := Real.pi_pos
    apply div_pos _ ha
    nlinarith
  · subst ha; rw [discI_zero hR.le]; have := Real.pi_pos; positivity

theorem discI_scale {a R t : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (ht : 0 < t) :
    discI (t * a) (R / Real.sqrt t) = discI a R / t := by
  have hs : (R / Real.sqrt t) ^ 2 = R ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hR' : 0 ≤ R / Real.sqrt t := div_nonneg hR (Real.sqrt_nonneg t)
  rcases ha.lt_or_eq with ha | ha
  · rw [discI_of_pos (mul_pos ht ha) hR', discI_of_pos ha hR, hs]
    have : t * a * (R ^ 2 / t) = a * R ^ 2 := by field_simp
    rw [this]
    field_simp
  · subst ha; rw [mul_zero, discI_zero hR', discI_zero hR, hs]; ring

theorem pgds_circle {R s : ℝ} (hs : 0 < s) (hsR : s < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) :
    2 * Real.pi * ‖g 0‖ ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := by
  have hpi := Real.pi_pos
  set h : ℂ → ℂ := fun z => g z ^ 2 with hh
  have habs : |s| = s := abs_of_pos hs
  have hdiff : DiffContOnCl ℂ h (Metric.ball 0 |s|) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by rw [habs]; exact hs.ne'), habs]
    exact (hg.pow 2).mono (Metric.closedBall_subset_ball hsR)
  have hav := hdiff.circleAverage
  rw [Real.circleAverage_def] at hav
  have hper : Function.Periodic (fun θ => ‖h (circleMap 0 s θ)‖) (2 * Real.pi) := by
    intro θ; simp only; rw [periodic_circleMap 0 s θ]
  have e1 := hper.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at e1
  have hle : ‖h 0‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (circleMap 0 s θ)‖ := by
    rw [← hav, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
  rw [e1, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo] at hle
  have hcm : ∀ θ : ℝ, circleMap 0 s θ = Complex.polarCoord.symm (s, θ) := by
    intro θ
    simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp only [hcm, hh, norm_pow] at hle
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)] at hle
  linarith

theorem disc_mean_le {R r : ℝ} (hr : 0 < r) (hrR : r < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) (w : ℝ → ℝ) (hwc : Continuous w)
    (hw : ∀ s, 0 ≤ w s) :
    ‖g 0‖ ^ 2 * ∫ z in Metric.ball (0 : ℂ) r, w ‖z‖ ≤
      ∫ z in Metric.ball (0 : ℂ) r, ‖g z‖ ^ 2 * w ‖z‖ := by
  have hgc : ContinuousOn g (Metric.closedBall 0 r) :=
    hg.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  obtain ⟨hiR, eR⟩ := pgds_integral_ball_polar (r := r) (fun z => ‖g z‖ ^ 2 * w ‖z‖)
    ((hgc.norm.pow 2).mul (hwc.comp continuous_norm).continuousOn)
  obtain ⟨-, eL⟩ := pgds_integral_ball_polar (r := r) (fun z => w ‖z‖)
    (hwc.comp continuous_norm).continuousOn
  rw [eL, eR, ← integral_const_mul]
  have hI : Integrable (fun p : ℝ × ℝ => p.1 * (‖g (Complex.polarCoord.symm p)‖ ^ 2 *
      w ‖Complex.polarCoord.symm p‖))
      ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hiR
  refine integral_mono_of_nonneg ?_ hI.integral_prod_left ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioo
      fun θ _ => mul_nonneg hs.1.le (hw _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have key := pgds_circle hs.1 (hs.2.trans hrR) g hg
    simp only [Complex.norm_polarCoord_symm, abs_of_pos hs.1]
    rw [setIntegral_const]
    simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    have e : ∀ θ : ℝ, s * (‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 * w s) =
        (s * w s) * ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := fun θ => by ring
    simp only [e]
    rw [integral_const_mul]
    have hsw : 0 ≤ s * w s := mul_nonneg hs.1.le (hw s)
    have := mul_le_mul_of_nonneg_left key hsw
    nlinarith

end ReciprocityTheory.GeometryOfNumbersTheory
