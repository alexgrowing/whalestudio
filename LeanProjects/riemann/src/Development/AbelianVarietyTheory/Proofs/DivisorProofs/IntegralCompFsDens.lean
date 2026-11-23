import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo
open MeasureTheory MvPolynomial GlobalTheory.FibLine

noncomputable section

namespace GlobalTheory.FibLine

theorem integral_comp_fsDens (g : ℝ → ℂ) (_hg : ContinuousOn g (Set.Icc 0 1)) :
    ∫ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * (fsDens x : ℂ) = ∫ t in (0 : ℝ)..1, g t := by
  set F : ℝ → ℂ := fun r => g (1 / (1 + r ^ 2)) * ((1 / (Real.pi * (1 + r ^ 2) ^ 2) : ℝ) : ℂ) with hF
  have h1 : ∫ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * (fsDens x : ℂ) = ∫ x : ℂ, F ‖x‖ := rfl
  rw [h1, integral_fun_norm_addHaar (volume : Measure ℂ) F]
  set f : ℝ → ℝ := fun r => (1 + r ^ 2)⁻¹ with hf
  set f' : ℝ → ℝ := fun r => -(2 * r) / (1 + r ^ 2) ^ 2 with hf'
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (f' x) (Set.Ioi 0) x := by
    intro x _
    have h : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    exact (h.inv hne).hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro a ha b hb hab
    simp only [hf, inv_inj, add_right_inj] at hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have himg : f '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : (0:ℝ) < r := hr
      refine ⟨by positivity, ?_⟩
      exact inv_lt_one_of_one_lt₀ (by nlinarith)
    · rintro ⟨h0, h1⟩
      have ht : 1 < t⁻¹ := one_lt_inv_iff₀.2 ⟨h0, h1⟩
      refine ⟨Real.sqrt (t⁻¹ - 1), Real.sqrt_pos.2 (by linarith), ?_⟩
      simp only [hf]
      rw [Real.sq_sqrt (by linarith)]
      simp
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [himg] at hcv
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hcv]
  have hvol : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [hvol, Complex.finrank_real_complex, nsmul_eq_mul, ← integral_smul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0:ℝ) < r := hr
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpos : (0:ℝ) < 1 + r ^ 2 := by positivity
  have habs : |f' r| = 2 * r / (1 + r ^ 2) ^ 2 := by
    simp only [hf']
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [habs]
  simp only [hF, hf, one_div, pow_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hpi' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpi
  have hpos' : ((1 : ℂ) + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp
  ring

end GlobalTheory.FibLine
