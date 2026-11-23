import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

open Set

theorem integrableOn_cpow_mul_exp_neg_mul {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x))) (Ioi 0) := by
  have h := Complex.GammaIntegral_convergent hw
  rw [← mul_zero c, ← integrableOn_Ioi_comp_mul_left_iff _ _ hc] at h
  refine (IntegrableOn.congr_fun (h.const_mul (1 / (c : ℂ) ^ (w - 1)))
    (fun t (ht : 0 < t) => ?_) measurableSet_Ioi)
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le ht.le, Complex.ofReal_exp]
  push_cast
  have hne : (c : ℂ) ^ (w - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.mpr hc.ne')
  field_simp

theorem exp_smul_integrand (w : ℂ) (c t : ℝ) :
    |Real.exp t| • (((Real.exp t : ℝ) : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * (Real.exp t : ℝ)))) =
      Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  rw [Complex.ofReal_exp]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem gamma_integral_exp_substitution :
    ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  intro r hr w hw
  set c : ℝ := 2 * Real.pi * r with hcdef
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x)) with hg
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp univ := fun x _ y _ h => Real.exp_injective h
  have hfun : (fun t : ℝ => |Real.exp t| • g (Real.exp t)) =
      fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
    funext t
    exact exp_smul_integrand w c t
  constructor
  · have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj g).mp
      (by rw [himg]; exact integrableOn_cpow_mul_exp_neg_mul hw hc)
    rw [hfun, integrableOn_univ] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj g
    rw [himg, hfun, Measure.restrict_univ] at h2
    rw [← h2, hg, Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hc, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg, mul_comm]

end GlobalTheory.HeckeMellin
