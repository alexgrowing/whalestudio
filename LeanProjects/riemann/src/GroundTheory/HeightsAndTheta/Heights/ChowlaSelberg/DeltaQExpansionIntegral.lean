import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries ArithmeticFunction
open scoped MatrixGroups ArithmeticFunction.sigma

noncomputable section

def DeltaQExpansionIntegral.Statement : Prop :=
  ∃ D : PowerSeries ℤ, constantCoeff D = 1 ∧
    qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) (X * D)

namespace DeltaQExpansionIntegral

def sigmaSeries (k : ℕ) : PowerSeries ℤ := mk fun n ↦ (σ k n : ℤ)

theorem qExpansion_E₄ :
    qExpansion 1 E₄ = map (Int.castRingHom ℂ) (1 + (240 : ℤ) • sigmaSeries 3) := by
  ext m
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, coeff_map]
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sigmaSeries]
  · rw [map_add, map_zsmul]
    simp [hm, sigmaSeries, hb, coeff_one]
    norm_num

theorem qExpansion_E₆ :
    qExpansion 1 E₆ = map (Int.castRingHom ℂ) (1 - (504 : ℤ) • sigmaSeries 5) := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, coeff_map]
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sigmaSeries]
  · rw [map_sub, map_zsmul]
    simp [hm, sigmaSeries, hb, coeff_one]
    norm_num

theorem twelve_dvd (n : ℕ) : 12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  rw [sigma_apply, sigma_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  generalize (d : ZMod 12) = x
  revert x
  decide

def cSeries : PowerSeries ℤ := mk fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)

theorem twelve_smul_cSeries :
    (12 : ℤ) • cSeries = (5 : ℤ) • sigmaSeries 3 + (7 : ℤ) • sigmaSeries 5 := by
  ext n
  have h := Nat.mul_div_cancel' (twelve_dvd n)
  rw [map_add, map_zsmul, map_zsmul, map_zsmul]
  simp only [cSeries, sigmaSeries, coeff_mk, smul_eq_mul]
  exact_mod_cast h

theorem qExpansion_discriminant_smul :
    (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  have e : (1728 : ℂ) • (⇑CuspForm.discriminant) = ⇑(E₄.pow 3) - ⇑(E₆.pow 2) := by
    funext τ
    simp only [Pi.smul_apply, Pi.sub_apply, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul,
      CuspForm.coe_discriminant, discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3,
    ← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2,
    ← ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL (E₄.pow 3) (E₆.pow 2), ← e,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ) CuspForm.discriminant]
  rfl

theorem proof : Statement := by
  set A := sigmaSeries 3
  set B := sigmaSeries 5
  set Ez : PowerSeries ℤ := 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2 + cSeries with hEz
  have hC := twelve_smul_cSeries
  simp only [zsmul_eq_mul, Int.cast_ofNat] at hC
  have hring : (1 + (240 : ℤ) • A) ^ 3 - (1 - (504 : ℤ) • B) ^ 2 = 1728 * Ez := by
    simp only [zsmul_eq_mul, Int.cast_ofNat, hEz]
    linear_combination (-144 : PowerSeries ℤ) * hC
  have key : qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) Ez := by
    have h2 : (1728 : ℂ) • map (Int.castRingHom ℂ) Ez = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
      rw [qExpansion_E₄, qExpansion_E₆, ← map_pow, ← map_pow, ← map_sub, hring, map_mul,
        map_ofNat, Algebra.smul_def, map_ofNat]
    exact smul_right_injective _ (by norm_num : (1728 : ℂ) ≠ 0)
      (qExpansion_discriminant_smul.trans h2.symm)
  have h0 : constantCoeff Ez = 0 := by
    simp [hEz, A, B, sigmaSeries, cSeries]
  obtain ⟨D, hD⟩ := X_dvd_iff.mpr h0
  refine ⟨D, ?_, hD ▸ key⟩
  have h1 := discriminant_qExpansion_coeff_one
  rw [key, hD, coeff_map, coeff_succ_X_mul, eq_intCast] at h1
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact_mod_cast h1

end DeltaQExpansionIntegral

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
