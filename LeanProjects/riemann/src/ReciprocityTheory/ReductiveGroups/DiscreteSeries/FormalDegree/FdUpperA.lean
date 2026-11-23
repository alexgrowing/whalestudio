import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_integral_exp_norm {c : ℝ} (hc : 0 < c) :
    ∫ x : ℂ, Real.exp (-c * ‖x‖) = Real.pi * c ^ (-2 : ℝ) * Real.Gamma 3 := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 1) le_rfl hc
  have e1 : (-2 / (1 : ℝ)) = -2 := by norm_num
  have e2 : (2 / (1 : ℝ) + 1) = 3 := by norm_num
  simp only [Real.rpow_one, e1, e2] at h
  exact h

theorem fdU_integrable_exp_norm {c : ℝ} (hc : 0 < c) : Integrable (fun x : ℂ => Real.exp (-c * ‖x‖)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_exp_norm hc]
  exact (mul_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hc _))
    (Real.Gamma_pos_of_pos (by norm_num))).ne'

theorem fdU_integral_gauss {b : ℝ} (hb : 0 < b) : ∫ x : ℂ, Real.exp (-b * ‖x‖ ^ 2) = Real.pi / b := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 2) (by norm_num) hb
  have e1 : (-2 / (2 : ℝ)) = -1 := by norm_num
  have e2 : (2 / (2 : ℝ) + 1) = 2 := by norm_num
  simp only [Real.rpow_two, e1, e2, Real.rpow_neg_one, Real.Gamma_two, mul_one] at h
  rw [h, div_eq_mul_inv]

theorem fdU_integrable_gauss {b : ℝ} (hb : 0 < b) : Integrable (fun x : ℂ => Real.exp (-b * ‖x‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_gauss hb]
  exact (div_pos Real.pi_pos hb).ne'

theorem fdU_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  have h : ((ab.1.2 : ℕ) : ℝ) < ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast ab.2.1
  simp only [wab, Pi.zero_apply]
  linarith

theorem exp_neg_quadratic_eq_prod {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Real.exp (-Qf (0 : Fin n → ℝ) y) =
      ∏ ab : PCoord ε, Real.exp (-wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2) := by
  simp only [Qf, ← Finset.sum_neg_distrib, Real.exp_sum, neg_mul]

theorem fdU_integrable_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2)) := by
  exact Integrable.fintype_prod
    (f := fun ab (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2)) (fun ab => fdU_integrable_gauss (hb ab))

theorem fdU_integral_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    ∫ y : PCoord ε → ℂ, ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2) = ∏ ab : PCoord ε, Real.pi / b ab := by
  exact (integral_fintype_prod_eq_prod
    (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2))).trans
    (Finset.prod_congr rfl fun ab _ => fdU_integral_gauss (hb ab))

theorem fdU_lintegral_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  have hb : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 :=
    fun ab => fdU_wab_zero_pos ab
  have hint : Integrable (fun y : PCoord ε → ℂ => Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
    simp_rw [exp_neg_quadratic_eq_prod]
    exact fdU_integrable_prod_gauss _ hb
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
  congr 1
  simp_rw [exp_neg_quadratic_eq_prod]
  rw [fdU_integral_prod_gauss _ hb]
  rfl

theorem fdU_integrable_prod_exp {ε : Fin n → Bool} {c : ℝ} (hc : ∀ _ : PCoord ε, 0 < c) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-c * ‖y ab‖)) := by
  exact Integrable.fintype_prod
    (f := fun _ (x : ℂ) => Real.exp (-c * ‖x‖)) (fun ab => fdU_integrable_exp_norm (hc ab))

end ReciprocityTheory.ChartRestriction.DS
