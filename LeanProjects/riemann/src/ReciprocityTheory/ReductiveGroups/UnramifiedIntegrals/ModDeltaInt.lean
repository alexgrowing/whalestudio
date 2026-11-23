import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem twelve_dvd_five_pow_three_add_seven_pow_five (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have key : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * d ^ 3 + 7 * d ^ 5) 12).mp
    (by push_cast; exact key _)
  exact_mod_cast h

theorem sigma_congr (n : ℕ) :
    (12 : ℤ) ∣ 5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => twelve_dvd_five_pow_three_add_seven_pow_five _

def s3Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 3 n : ℤ)

def s5Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 5 n : ℤ)

def tZ : PowerSeries ℤ := PowerSeries.mk fun n =>
  (5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ)) / 12

theorem eisensteinFourInt_eq : e4Z = 1 + PowerSeries.C (240 : ℤ) * s3Z := by
  ext n
  simp only [e4Z, s3Z, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem eisensteinSixInt_eq : e6Z = 1 - PowerSeries.C (504 : ℤ) * s5Z := by
  ext n
  simp only [e6Z, s5Z, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem tZ_mul : PowerSeries.C (12 : ℤ) * tZ =
    PowerSeries.C (5 : ℤ) * s3Z + PowerSeries.C (7 : ℤ) * s5Z := by
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, tZ, s3Z, s5Z, PowerSeries.coeff_mk]
  exact Int.mul_ediv_cancel' (sigma_congr n)

theorem eisenstein_cube_sub_sq_eq : e4Z ^ 3 - e6Z ^ 2 = PowerSeries.C (1728 : ℤ) *
    (tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 + PowerSeries.C (8000 : ℤ) * s3Z ^ 3
      - PowerSeries.C (147 : ℤ) * s5Z ^ 2) := by
  have h := tZ_mul
  rw [eisensteinFourInt_eq, eisensteinSixInt_eq]
  simp only [map_ofNat] at h ⊢
  linear_combination (-144 : PowerSeries ℤ) * h

theorem dZ_mul : PowerSeries.C (1728 : ℤ) * dZ = e4Z ^ 3 - e6Z ^ 2 := by
  ext n
  rw [PowerSeries.coeff_C_mul, dZ, PowerSeries.coeff_mk, eisenstein_cube_sub_sq_eq, PowerSeries.coeff_C_mul]
  exact Int.mul_ediv_cancel' (dvd_mul_right _ _)

private theorem dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq : dZ = tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 +
    PowerSeries.C (8000 : ℤ) * s3Z ^ 3 - PowerSeries.C (147 : ℤ) * s5Z ^ 2 := by
  have h := dZ_mul.trans eisenstein_cube_sub_sq_eq
  refine mul_left_cancel₀ (fun h0 => ?_) h
  have := congrArg PowerSeries.constantCoeff h0
  rw [PowerSeries.constantCoeff_C, map_zero] at this
  norm_num at this

theorem dZ_coeff_zero : PowerSeries.coeff 0 dZ = 0 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dZ_coeff_one : PowerSeries.coeff 1 dZ = 1 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dC_eq : dC = qExpansion 1 DD := by
  have h4 : qExpansion 1 ⇑((E₄.mul E₄).mul E₄) = qExpansion 1 E₄ ^ 3 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp), ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have h6 : qExpansion 1 ⇑(E₆.mul E₆) = qExpansion 1 E₆ ^ 2 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have hfun : DD = ⇑((1 / 1728 : ℂ) • ((E₄.mul E₄).mul E₄)) - ⇑((1 / 1728 : ℂ) • (E₆.mul E₆)) := by
    funext τ
    simp only [DD, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, Pi.sub_apply,
      ModularForm.coe_smul, ModularForm.coe_mul, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hd := congrArg (PowerSeries.map (Int.castRingHom ℂ)) dZ_mul
  rw [map_mul, map_sub, map_pow, map_pow, PowerSeries.map_C, map_eisensteinFourInt, map_eisensteinSixInt] at hd
  rw [hfun, ModularForm.qExpansion_sub one_pos (by simp), ModularForm.coe_smul, ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos (by simp), ModularForm.qExpansion_smul one_pos (by simp),
    h4, h6, ← smul_sub, ← hd, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  rw [show (1 / 1728 : ℂ) * (Int.castRingHom ℂ) 1728 = 1 by norm_num, map_one, one_mul]
  rfl

end ReciprocityTheory.ChartRestriction.L1
