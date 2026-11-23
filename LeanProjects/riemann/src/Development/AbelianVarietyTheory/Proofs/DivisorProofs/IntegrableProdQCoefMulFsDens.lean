import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine.Intg

theorem integrable_fsDens : Integrable fsDens := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (h.const_mul (1 / Real.pi)).congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have e : (-4 / 2 : ℝ) = -((2 : ℕ) : ℝ) := by norm_num
  simp only [fsDens]
  rw [e, Real.rpow_neg hx.le, Real.rpow_natCast]
  have := Real.pi_pos
  field_simp

theorem continuous_lineVec (a : Fin 2) : Continuous fun x : ℂ => lineVec x a := by
  fin_cases a
  · simpa [lineVec] using continuous_const
  · simpa [lineVec] using continuous_id'

theorem continuous_qCoef (ab : Fin 2 × Fin 2) : Continuous fun x : ℂ => qCoef x ab := by
  unfold qCoef
  refine Continuous.div ((continuous_lineVec _).mul (Complex.continuous_conj.comp (continuous_lineVec _)))
    (Complex.continuous_ofReal.comp (by fun_prop)) fun x => ?_
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  exact_mod_cast hx.ne'

theorem norm_lineVec_sq_le (x : ℂ) (a : Fin 2) : ‖lineVec x a‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
  fin_cases a
  · simp [lineVec]
  · simp [lineVec]

theorem norm_qCoef_le (x : ℂ) (ab : Fin 2 × Fin 2) : ‖qCoef x ab‖ ≤ 1 := by
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  unfold qCoef
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx.le, div_le_one hx]
  have h1 := norm_lineVec_sq_le x ab.1
  have h2 := norm_lineVec_sq_le x ab.2
  nlinarith [sq_nonneg (‖lineVec x ab.2‖ - ‖lineVec x ab.1‖)]

theorem integrable_prod_qCoef_mul_fsDens (k : ℕ) (f : Fin k → Fin 2 × Fin 2) :
    Integrable (fun x : ℂ => (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) := by
  have h : Integrable (fun x : ℂ => (fsDens x : ℂ)) := integrable_fsDens.ofReal
  refine h.bdd_mul (c := 1) (continuous_finset_prod _ fun i _ => continuous_qCoef (f i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => norm_qCoef_le x (f i)

end GlobalTheory.FibLine.Intg
