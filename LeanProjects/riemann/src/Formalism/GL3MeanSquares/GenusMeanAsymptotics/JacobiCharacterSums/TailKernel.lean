import Mathlib

open Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem norm_exp_sub_one_le_of_re_nonneg (u : ℂ) (hu : 0 ≤ u.re) :
    ‖Complex.exp u - 1‖ ≤ Real.exp u.re * ‖u‖ := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => Complex.exp ((t : ℂ) * u)) (f' := fun t : ℝ => Complex.exp ((t : ℂ) * u) * u)
    (C := Real.exp u.re * ‖u‖) (a := 0) (b := 1)
    (fun t _ => by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).mul_const u
      exact h1.cexp.hasDerivWithinAt)
    (fun t ht => by
      rw [norm_mul, Complex.norm_exp]
      have hre : ((t : ℂ) * u).re = t * u.re := by simp
      rw [hre]
      gcongr
      nlinarith [ht.1, ht.2])
    1 (by simp)
  simpa using key

theorem tail_kernel_cpow (y η : ℝ) (hy : 0 < y) (hη : 0 ≤ η) (hη1 : η ≤ 1) (w : ℂ) (hw0 : 0 ≤ w.re)
    (hw2 : w.re ≤ 2) :
    ‖((y * (1 + η) : ℝ) : ℂ) ^ w - (y : ℂ) ^ w‖ ≤ 4 * η * ‖w‖ * y ^ w.re := by
  have hy1 : (0 : ℝ) < 1 + η := by linarith
  have hL0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have hLη : Real.log (1 + η) ≤ η := by
    have := Real.log_le_sub_one_of_pos hy1
    linarith
  have hL2 : Real.log (1 + η) ≤ Real.log 2 := Real.log_le_log hy1 (by linarith)
  have hsplit : ((y * (1 + η) : ℝ) : ℂ) ^ w = (y : ℂ) ^ w * ((1 + η : ℝ) : ℂ) ^ w := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hy.le hy1.le w
  have hpow : ((1 + η : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log (1 + η) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy1.ne'), ← Complex.ofReal_log hy1.le, mul_comm]
  have hre : 0 ≤ (w * (Real.log (1 + η) : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hw0 hL0
  have hb := norm_exp_sub_one_le_of_re_nonneg _ hre
  have hre' : (w * (Real.log (1 + η) : ℂ)).re = w.re * Real.log (1 + η) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hnorm : ‖w * (Real.log (1 + η) : ℂ)‖ = ‖w‖ * Real.log (1 + η) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  have hexp : Real.exp (w.re * Real.log (1 + η)) ≤ 4 := by
    have h4 : Real.exp (2 * Real.log 2) = 4 := by
      rw [two_mul, Real.exp_add, Real.exp_log two_pos]; norm_num
    rw [← h4]
    apply Real.exp_le_exp.mpr
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  rw [hre', hnorm] at hb
  have hyw : ‖(y : ℂ) ^ w‖ = y ^ w.re := Complex.norm_cpow_eq_rpow_re_of_pos hy w
  have hypos : 0 ≤ y ^ w.re := Real.rpow_nonneg hy.le _
  rw [hsplit, hpow, ← mul_sub_one, norm_mul, hyw]
  calc y ^ w.re * ‖Complex.exp (w * (Real.log (1 + η) : ℂ)) - 1‖
      ≤ y ^ w.re * (Real.exp (w.re * Real.log (1 + η)) * (‖w‖ * Real.log (1 + η))) := by gcongr
    _ ≤ y ^ w.re * (4 * (‖w‖ * η)) := by
        gcongr
    _ = 4 * η * ‖w‖ * y ^ w.re := by ring

theorem tail_kernel_norm_lower (σ u : ℝ) (hσ1 : σ ≤ 1 - 1 / 800) :
    (1 / 800 + |u|) / 2 ≤ ‖(σ : ℂ) + (u : ℂ) * I - 1‖ := by
  have h1 := Complex.abs_re_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
  have h2 := Complex.abs_im_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add] at h1 h2
  have hre : 1 / 800 ≤ |σ - 1| := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  linarith

theorem tail_kernel_half (T : ℝ) (hT : 0 ≤ T) :
    ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + u) = 2 * Real.log (1 + 800 * T) := by
  have hfun : (fun u : ℝ => 2 / (1 / 800 + u)) = fun u => 2 * (u + 1 / 800)⁻¹ := by
    funext u; rw [div_eq_mul_inv, add_comm]
  have hsh := intervalIntegral.integral_comp_add_right (a := 0) (b := T) (fun x : ℝ => x⁻¹) (1 / 800)
  rw [hfun, intervalIntegral.integral_const_mul, hsh,
    integral_inv_of_pos (by norm_num) (by linarith)]
  congr 2
  field_simp
  ring

theorem tail_kernel_line (σ T : ℝ) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1 - 1 / 800) (hT : 0 ≤ T) :
    ∫ u in (-T)..T, 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖ ≤ 4 * Real.log (1 + 800 * T) := by
  have hg : Continuous (fun u : ℝ => 2 / (1 / 800 + |u|)) :=
    Continuous.div continuous_const (continuous_const.add continuous_abs) (fun x => by positivity)
  have hne : ∀ u : ℝ, ‖(σ : ℂ) + (u : ℂ) * I - 1‖ ≠ 0 := by
    intro u
    have := tail_kernel_norm_lower σ u hσ1
    have : 0 < (1 / 800 + |u|) / 2 := by positivity
    linarith
  have hf : Continuous (fun u : ℝ => 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖) :=
    Continuous.div continuous_const
      (((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).norm) hne
  calc ∫ u in (-T)..T, 1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖
      ≤ ∫ u in (-T)..T, 2 / (1 / 800 + |u|) := by
        apply intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
          (hg.intervalIntegrable _ _)
        intro u _
        have h3 := tail_kernel_norm_lower σ u hσ1
        have hp : 0 < (1 / 800 + |u|) / 2 := by positivity
        have := one_div_le_one_div_of_le hp h3
        rwa [one_div_div] at this
    _ = 4 * Real.log (1 + 800 * T) := by
        have hsplit := (intervalIntegral.integral_add_adjacent_intervals (a := -T) (b := 0) (c := T)
          (hg.intervalIntegrable (μ := MeasureTheory.volume) _ _)
          (hg.intervalIntegrable (μ := MeasureTheory.volume) _ _))
        have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := T)
          (fun u : ℝ => 2 / (1 / 800 + |u|))
        simp only [neg_zero, abs_neg] at hneg
        have hpos : ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + |u|) = ∫ u in (0 : ℝ)..T, 2 / (1 / 800 + u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le hT] at hu
          simp only [abs_of_nonneg hu.1]
        rw [← hsplit, ← hneg, hpos, tail_kernel_half T hT]
        ring

end Formalism.HermitianLattices.Ext.BoxTail
