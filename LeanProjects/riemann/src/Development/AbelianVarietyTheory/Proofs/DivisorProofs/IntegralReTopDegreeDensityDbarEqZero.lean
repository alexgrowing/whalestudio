import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

theorem integrable_dbar_integral_eq_zero {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem dens_dbarAt_eq_sum {n : ℕ} (F : V n → Alt n) (v : V n) :
    dens (dbarAt F v) = ∑ a, ∑ S, dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) := by
  simp only [dens, dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_re_dens_dbarAt_eq_zero {n : ℕ} (F : V n → Alt n)
    (hF : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S)) (hc : HasCompactSupport F) :
    ∫ v, (dens (dbarAt F v)).re = 0 := by
  have h (a : Fin n) (S : Finset (Fin (n + n))) :=
    integrable_dbar_integral_eq_zero (hF S)
      (hc.comp_left (g := fun α : Alt n => (bas n).repr α S) (by simp)) (coordVec a)
  have hi (a : Fin n) (S : Finset (Fin (n + n))) :
      Integrable fun v => dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) :=
    (h a S).1.mul_const _
  have hD : Integrable fun v => dens (dbarAt F v) := by
    simp only [dens_dbarAt_eq_sum]
    exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S
  have h0 : ∫ v, dens (dbarAt F v) = 0 := by
    simp only [dens_dbarAt_eq_sum]
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finset_sum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [integral_mul_const, (h a S).2, zero_mul]
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm
