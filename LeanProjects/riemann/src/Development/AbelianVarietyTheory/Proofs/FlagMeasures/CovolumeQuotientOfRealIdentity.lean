import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem covolQuotient_real (d : ℝ) (f t : ℕ) (hd : 1 ≤ d) :
    ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2) =
      ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) *
        ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) := by
  have hd0 : 0 < d := by linarith
  have hd0' : d ≠ 0 := hd0.ne'
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0.le

  have h1 : d ^ (1 / 2 - 2 * (t : ℝ)) = Real.sqrt d / d ^ (2 * t) := by
    rw [Real.rpow_sub hd0, Real.sqrt_eq_rpow]
    congr 1
    exact_mod_cast Real.rpow_natCast d (2 * t)
  rw [Real.sqrt_sq hd0.le, h1]
  calc ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * d
      = ((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * (Real.sqrt d * Real.sqrt d) := by rw [hs]
    _ = _ := by
        rw [← pow_mul, show 2 * (2 * t) = 2 * t + 2 * t by ring, pow_add]
        field_simp

theorem covolQuotient_arith : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c →
    ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) =
      ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m →
    ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  intro d c f t m hd hc h
  have hd0 : 0 < d := by linarith
  have hY : 0 < (d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d :=
    mul_pos (mul_pos (inv_pos.mpr (pow_pos hd0 _)) (by norm_num)) (Real.sqrt_pos.mpr hd0)
  have hZ : 0 ≤ (2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hd0.le _)

  rw [covolQuotient_real d f t hd, ENNReal.ofReal_mul hY.le] at h
  have hm : m = ENNReal.ofReal ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ))) :=
    ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hY).ne' ENNReal.ofReal_ne_top).mp h).symm
  rw [hm, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) f)]
  congr 1
  have h2 : (2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f = 1 := by rw [← mul_pow]; norm_num
  calc (2 * c) ^ f * ((2⁻¹ : ℝ) ^ f * d ^ (1 / 2 - 2 * (t : ℝ)))
      = ((2 : ℝ) ^ f * (2⁻¹ : ℝ) ^ f) * (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by ring
    _ = d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f := by rw [h2, one_mul]

end GlobalTheory
