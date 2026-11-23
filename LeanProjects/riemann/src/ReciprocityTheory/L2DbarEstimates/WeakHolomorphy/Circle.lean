import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem measurePreserving_smul_unit {n : ℕ} (a : ℂ) (ha : ‖a‖ = 1) :
    MeasurePreserving (fun z : V n => a • z) volume volume := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let L : V n ≃ₗᵢ[ℝ] V n :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ (V n) a ha0).restrictScalars ℝ
      norm_map' := fun z => by simp [norm_smul, ha] }
  have hL : (fun z : V n => a • z) = L := by
    funext z
    rfl
  rw [hL]
  exact L.measurePreserving

theorem circle_mean {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (c + Complex.exp ((θ : ℂ) * I) • w) =
      ((2 * Real.pi : ℝ) : ℂ) * u c := by
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hρ1 : 1 < R / ‖w‖ := by
    rw [lt_div_iff₀ hwpos]
    linarith
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.ball 0 (R / ‖w‖)) := by
    intro ζ hζ
    have hmem : c + ζ • w ∈ ball c R := by
      rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hwpos] at hζ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact hζ
    have h1 : DifferentiableAt ℂ u (c + ζ • w) := hu.differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => c + ζ • w) ζ :=
      (differentiableAt_id.smul_const w).const_add c
    exact (h1.comp ζ h2).differentiableWithinAt
  have hcl : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.closedBall 0 1) :=
    hg.mono (Metric.closedBall_subset_ball hρ1)
  have key := hcl.circleIntegral_sub_inv_smul (w := 0) (by simp)
  simp only [circleIntegral, deriv_circleMap, sub_zero, smul_eq_mul, zero_smul, add_zero] at key
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp ((θ : ℂ) * I) := by
    intro θ
    simp [circleMap]
  have h3 : ∀ θ : ℝ, circleMap 0 1 θ * I * ((circleMap 0 1 θ)⁻¹ * u (c + circleMap 0 1 θ • w)) =
      I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by
    intro θ
    have hne : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
    rw [hcm θ] at hne ⊢
    calc Complex.exp ((θ : ℂ) * I) * I * ((Complex.exp ((θ : ℂ) * I))⁻¹ * u (c + Complex.exp ((θ : ℂ) * I) • w))
        = I * u (c + Complex.exp ((θ : ℂ) * I) • w) * (Complex.exp ((θ : ℂ) * I) * (Complex.exp ((θ : ℂ) * I))⁻¹) := by ring
      _ = I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by rw [mul_inv_cancel₀ hne, mul_one]
  simp only [h3, intervalIntegral.integral_const_mul] at key
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [key]
  push_cast
  ring

theorem circle_mean_sq {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖u (c + Complex.exp ((θ : ℂ) * I) • w)‖ₑ ^ 2 := by
  have hmem : ∀ θ : ℝ, c + Complex.exp ((θ : ℂ) * I) • w ∈ ball c R := by
    intro θ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hw
  set F : ℝ → ℂ := fun θ => u (c + Complex.exp ((θ : ℂ) * I) • w) with hF
  have hcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    have h1 := (hu.differentiableAt (isOpen_ball.mem_nhds (hmem θ))).continuousAt
    have h2 : Continuous fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w := by fun_prop
    show ContinuousAt (u ∘ fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) θ
    exact ContinuousAt.comp (f := fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) (x := θ) h1
      h2.continuousAt
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hI : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ = ((2 * Real.pi : ℝ) : ℂ) * u c := by
    rw [← intervalIntegral.integral_of_le hpi]
    exact circle_mean hu hw
  have hint : IntegrableOn F (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun θ => ‖F θ‖ ^ 2) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    ((hcont.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcr : Continuous fun θ => (F θ * (starRingEnd ℂ) (u c)).re :=
    Complex.continuous_re.comp (hcont.mul continuous_const)
  have hint3 : IntegrableOn (fun θ => (F θ * (starRingEnd ℂ) (u c)).re) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcr.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpt : ∀ θ, 2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2 ≤ ‖F θ‖ ^ 2 := by
    intro θ
    have h := Complex.normSq_nonneg (F θ - u c)
    rw [Complex.normSq_sub] at h
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  have hre : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
      2 * Real.pi * ‖u c‖ ^ 2 := by
    have h1 : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
        (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ * (starRingEnd ℂ) (u c)).re :=
      integral_re (hint.mul_const _)
    rw [h1, integral_mul_const, hI, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hreal : ‖u c‖ ^ 2 * (2 * Real.pi) ≤ ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 := by
    have h : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2) ≤
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 :=
      integral_mono ((hint3.const_mul 2).sub (integrable_const (‖u c‖ ^ 2))) hint2 hpt
    rw [integral_sub (hint3.const_mul 2) (integrable_const _), integral_const_mul, hre,
      integral_const] at h
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, smul_eq_mul] at h
    have hv : (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real univ = 2 * Real.pi := by
      simp [Measure.real, Real.volume_Ioc, hpi, Real.pi_pos.le]
    rw [hv] at h
    linarith
  have hen : ∀ θ, ‖F θ‖ₑ ^ 2 = ENNReal.ofReal (‖F θ‖ ^ 2) := fun θ => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  show ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ₑ ^ 2
  simp_rw [hen]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun θ => by positivity),
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end ReciprocityTheory.L2DbarEstimates.C
