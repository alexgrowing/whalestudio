import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaDerivNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.ThetaA

noncomputable section

open Complex

namespace PI.SSE

lemma expo1 (v₁ p₁ A z : ℂ) (hv₁ : v₁ ≠ 0) (hA : A ≠ 0) :
    Real.pi * p₁ / (2 * A * v₁) * (z + v₁) ^ 2 =
      Real.pi * p₁ * (z + v₁ / 2) / A + Real.pi * p₁ / (2 * A * v₁) * z ^ 2 := by
  field_simp
  ring

lemma expo2 (v₁ v₂ p₁ p₂ A z : ℂ) (hv₁ : v₁ ≠ 0) (hA : A ≠ 0)
    (hI : I = (p₁ * v₂ - v₁ * p₂) / (2 * A)) :
    Real.pi * p₁ / (2 * A * v₁) * (z + v₂) ^ 2 +
        (-(Real.pi * I * (v₂ / v₁)) - 2 * Real.pi * I * (z / v₁)) =
      Real.pi * p₂ * (z + v₂ / 2) / A + Real.pi * p₁ / (2 * A * v₁) * z ^ 2 := by
  rw [hI]
  field_simp
  ring

lemma I_eq (v₁ v₂ : ℂ) (h : ((starRingEnd ℂ) v₁ * v₂).im ≠ 0) :
    I = ((starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂) /
      (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ)) := by
  have hc : (((starRingEnd ℂ) v₁ * v₂).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  have hsub : (starRingEnd ℂ) v₁ * v₂ - v₁ * (starRingEnd ℂ) v₂ = 2 * I * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) := by
    have h1 : v₁ * (starRingEnd ℂ) v₂ = (starRingEnd ℂ) ((starRingEnd ℂ) v₁ * v₂) := by
      simp [mul_comm]
    rw [h1, Complex.sub_conj]
    push_cast
    ring
  rw [hsub]
  field_simp

theorem genEqOf : GenEqOf := by
  intro hA hD v₁ v₂ hv₁ hτ h3
  have hAr : 0 < ((starRingEnd ℂ) v₁ * v₂).im := by
    have h1 := im_div_eq v₁ v₂
    have h2 : 0 < Complex.normSq v₁ := Complex.normSq_pos.mpr hv₁
    rw [h1] at hτ
    exact (div_pos_iff_of_pos_right h2).mp hτ
  have hA0 : (((starRingEnd ℂ) v₁ * v₂).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hAr.ne'
  obtain ⟨hdiff, hodd, hone, htau, hder⟩ := hA (v₂ / v₁) hτ
  have hc : jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) ≠ 0 := hD (v₂ / v₁) hτ h3
  have h0 : th (v₂ / v₁) 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linear_combination h / 2
  refine ⟨fun z => v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) *
      (cexp (Real.pi * (starRingEnd ℂ) v₁ / (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2) *
        th (v₂ / v₁) (z / v₁)), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Differentiable.cexp (by fun_prop)).mul (hdiff.comp (by fun_prop))).const_mul _
  · have hf : HasDerivAt (fun z : ℂ => cexp (Real.pi * (starRingEnd ℂ) v₁ /
        (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁) * z ^ 2)) 0 0 := by
      have h1 := ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi * (starRingEnd ℂ) v₁ /
        (2 * (((starRingEnd ℂ) v₁ * v₂).im : ℂ) * v₁))).cexp
      simpa using h1
    have h1 : HasDerivAt (th (v₂ / v₁)) (jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁)) (0 / v₁) := by
      rw [zero_div, ← hder]
      exact (hdiff 0).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => z / v₁) (1 / v₁) 0 := (hasDerivAt_id (0 : ℂ)).div_const v₁
    have hh := h1.comp (0 : ℂ) h2
    have hG := (hf.mul hh).const_mul (v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁))
    refine hG.deriv.trans ?_
    simp only [Function.comp_apply, zero_div, h0, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Complex.exp_zero, one_mul]
    generalize jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) = c at *
    field_simp
  · intro z
    simp only
    rw [neg_sq, neg_div, hodd]
    ring
  · intro z
    simp only
    have e1 : (z + v₁) / v₁ = z / v₁ + 1 := by field_simp
    rw [e1, hone, expo1 v₁ ((starRingEnd ℂ) v₁) _ z hv₁ hA0, Complex.exp_add]
    unfold qf
    ring
  · intro z
    simp only
    have key := expo2 v₁ v₂ ((starRingEnd ℂ) v₁) ((starRingEnd ℂ) v₂) _ z hv₁ hA0 (I_eq v₁ v₂ hAr.ne')
    rw [add_div, htau]
    rw [show ∀ x y t : ℂ, v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp x * -(cexp y * t)) =
        -(v₁ / jacobiTheta₂' (1 / 2 + v₂ / v₁ / 2) (v₂ / v₁) * (cexp (x + y) * t)) from
        fun x y t => by rw [Complex.exp_add]; ring, key, Complex.exp_add]
    unfold qf
    ring

end PI.SSE

end
