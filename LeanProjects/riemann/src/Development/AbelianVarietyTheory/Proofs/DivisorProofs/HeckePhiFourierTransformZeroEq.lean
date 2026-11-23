import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem phi_ofReal_mul (σ : ℂ) (y : ℝ) (w : ℂ) :
    phi σ ((y : ℂ) * w) = (((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg y) (norm_nonneg w)]
  have h : ((y : ℂ))⁻¹ ^ 2 = ((|y| : ℝ) : ℂ)⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, ← ofReal_pow, ← ofReal_pow, sq_abs]
  rw [mul_inv, mul_pow, h]
  ring

theorem hTrans_zero_eq (σ : ℂ) (y : ℝ) (hy : y ≠ 0) :
    hTrans σ 0 y = cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  have h0 : hTrans σ 0 y = ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) := by simp [hTrans]
  have h1 : cConst σ = ∫ t : ℝ, phi σ ((t : ℂ) + I) := by simp [cConst, hTrans]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) y
  have h2 : (∫ u : ℝ, phi σ (((y * u : ℝ) : ℂ) + (y : ℂ) * I)) =
      (((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) * ∫ u : ℝ, phi σ ((u : ℂ) + I) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext u
    rw [← phi_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [h2] at hsub
  have hya : (|y| : ℝ) ≠ 0 := abs_ne_zero.mpr hy
  have hyc : ((|y| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hya
  have h3 : (∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I)) =
      ((|y| : ℝ) : ℂ) * ((((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) *
        ∫ u : ℝ, phi σ ((u : ℂ) + I)) := by
    rw [hsub, abs_inv, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hyc, one_mul]
  have hc : ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) = ((|y| : ℝ) : ℂ)⁻¹ * ((|y| : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [show (-1 - 2 * σ) = -1 + -2 * σ by ring, cpow_add _ _ hyc, cpow_neg_one]
  rw [h0, h3, ← h1, hc]
  field_simp

end GlobalTheory.HeckeTwo
