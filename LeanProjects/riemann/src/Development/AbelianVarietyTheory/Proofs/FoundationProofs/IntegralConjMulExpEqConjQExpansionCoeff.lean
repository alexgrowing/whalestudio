import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Qc

lemma exp_eq_conj_qParam (T : ℝ) (n : ℕ) (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) =
      (starRingEnd ℂ) (1 / Function.Periodic.qParam T ((x : ℂ) + (y : ℂ) * Complex.I) ^ n) *
        (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, one_div, ← Complex.exp_neg, ← Complex.exp_conj,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, map_div₀, map_add, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  push_cast
  linear_combination (4 * (Real.pi : ℂ) * n * y / T) * Complex.I_sq

theorem conj_integral (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ) (hT : 0 < T) (hy : 0 < y)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (hper : Function.Periodic (h ∘ ofComplex) T)
    (hbdd : IsBoundedAtImInfty h) :
    (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
        Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) =
      T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  have hc : ∀ f : ℝ → ℂ, (starRingEnd ℂ) (∫ u in (0 : ℝ)..T, f u) = ∫ u in (0 : ℝ)..T, (starRingEnd ℂ) (f u) := by
    intro f
    rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le, integral_conj]
  rw [qExpansion_coeff_eq_intervalIntegral hT hper hhol hbdd n hy, map_mul, hc]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [show (starRingEnd ℂ) (1 / (T : ℂ)) = 1 / (T : ℂ) by simp [Complex.conj_ofReal],
    ← mul_assoc, mul_one_div_cancel hT', one_mul, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  simp only [ofComplex_apply_of_im_pos him]
  rw [exp_eq_conj_qParam, map_mul, ← mul_assoc, mul_comm ((starRingEnd ℂ) (h _))]
  rfl

end GlobalTheory.HeckeFamilyMatrices.Qc
