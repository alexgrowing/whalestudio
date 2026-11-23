import Mathlib

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem excTerm (x β : ℝ) (hx : 0 < x) (hL : 4 ≤ Real.log x) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1) :
    x ^ β / β ≤ x * (1 - (1 - β) / 2) := by
  have hβpos : 0 < β := by linarith
  have hsplit : x ^ β = x * x ^ (β - 1) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp
  have hy0 : 0 ≤ x ^ (β - 1) := Real.rpow_nonneg hx.le _
  have hyE : x ^ (β - 1) * Real.exp (4 * (1 - β)) ≤ 1 := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
    have hneg : Real.log x * (β - 1) + 4 * (1 - β) ≤ 0 := by nlinarith
    calc Real.exp (Real.log x * (β - 1) + 4 * (1 - β)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
      _ = 1 := Real.exp_zero
  have hE := Real.add_one_le_exp (4 * (1 - β))
  have hPpos : 0 ≤ β * (1 - (1 - β) / 2) := mul_nonneg hβpos.le (by linarith)
  have hP : 1 ≤ (4 * (1 - β) + 1) * (β * (1 - (1 - β) / 2)) := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hβ2) (sub_nonneg.2 hβ1))
      (by linarith : (0:ℝ) ≤ 5 / 2 + 2 * β), sub_nonneg.2 hβ2]
  have hEP : 1 ≤ Real.exp (4 * (1 - β)) * (β * (1 - (1 - β) / 2)) :=
    le_trans hP (mul_le_mul_of_nonneg_right hE hPpos)
  have hyP : x ^ (β - 1) ≤ β * (1 - (1 - β) / 2) := by
    calc x ^ (β - 1) = x ^ (β - 1) * 1 := (mul_one _).symm
      _ ≤ x ^ (β - 1) * (Real.exp (4 * (1 - β)) * (β * (1 - (1 - β) / 2))) :=
          mul_le_mul_of_nonneg_left hEP hy0
      _ = (x ^ (β - 1) * Real.exp (4 * (1 - β))) * (β * (1 - (1 - β) / 2)) := by ring
      _ ≤ 1 * (β * (1 - (1 - β) / 2)) := mul_le_mul_of_nonneg_right hyE hPpos
      _ = β * (1 - (1 - β) / 2) := one_mul _
  rw [hsplit, div_le_iff₀ hβpos]
  calc x * x ^ (β - 1) ≤ x * (β * (1 - (1 - β) / 2)) := mul_le_mul_of_nonneg_left hyP hx.le
    _ = x * (1 - (1 - β) / 2) * β := by ring

theorem excTerm_ofReal (x β : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) ^ (β : ℂ) / (β : ℂ) = ((x ^ β / β : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_cpow hx]

end Formalism.HermitianLattices.Ext.SupplyAP
