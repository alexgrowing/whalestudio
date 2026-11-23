import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem

open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory.InterpCurv

theorem del_log_sq_le_and_levi_log_le (ι : Type) [Fintype ι] (r : (ι → ℂ) → ℝ) (G : Matrix ι ι ℂ)
    (CP : ℝ) (z : ι → ℂ) (hr : ContDiffAt ℝ 2 r z) (h0 : 0 < r z) (hG : G.PosSemidef)
    (h1 : FormLe (fun ξ η => gradForm r z ξ η / ((r z : ℂ) ^ 2)) (fun ξ η => CP * formOf G ξ η))
    (h2 : FormAbsLe (ddc (fun x => Real.log (r x)) z) CP (formOf G)) (ξ : ι → ℂ) :
    ‖del (fun x => ((Real.log (r x) : ℝ) : ℂ)) z ξ‖ ^ 2 ≤ 2 * Real.pi * |CP| * gnorm G ξ ^ 2 ∧
      |(leviForm (fun x => Real.log (r x)) z ξ ξ).re| ≤ 2 * Real.pi * |CP| * gnorm G ξ ^ 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : 0 < 2 * Real.pi := by positivity
  have key : ∀ a : ℝ, a / (2 * Real.pi) ≤ CP * gnorm G ξ ^ 2 →
      a ≤ 2 * Real.pi * |CP| * gnorm G ξ ^ 2 := fun a ha => by
    rw [div_le_iff₀ h2π] at ha
    refine ha.trans ?_
    rw [mul_comm, mul_assoc (2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) h2π.le
  have hI : ∀ w : ℂ, -Complex.I * (kappa * w) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * w := fun w => by
    rw [kappa]; push_cast
    linear_combination (-w / (2 * Real.pi)) * Complex.I_mul_I
  refine ⟨key _ ?_, key _ ?_⟩
  · have hd := del_ofReal_comp (t := r) (z := z) (Real.hasDerivAt_log h0.ne')
      (hr.differentiableAt two_ne_zero) ξ
    have h3 : (r z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have h4 : -Complex.I * (gradForm r z ξ ξ / ((r z : ℂ) ^ 2)) =
        ((‖del (fun x => ((Real.log (r x) : ℝ) : ℂ)) z ξ‖ ^ 2 / (2 * Real.pi) : ℝ) : ℂ) := by
      rw [← mul_div_assoc, gradForm, hI, dbar_ofReal, hd]
      push_cast
      rw [← Complex.mul_conj']
      simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, map_inv₀]
      field_simp
    have h5 := diagVal_formOf_eq_gnorm_sq hG ξ
    have h6 := h1 ξ
    simp only [diagVal] at h5 h6
    rwa [h4, Complex.ofReal_re, mul_left_comm, Complex.re_ofReal_mul, h5] at h6
  · have h6 := formAbsLe_iff.1 h2 ξ
    rw [diagVal_formOf_eq_gnorm_sq hG, diagVal, ddc, hI, Complex.re_ofReal_mul, abs_mul,
      abs_of_pos (inv_pos.2 h2π)] at h6
    rwa [div_eq_inv_mul]

end GlobalTheory.InterpCurv
