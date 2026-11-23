import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

namespace GlobalTheory

theorem page_relation_deg_three : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CG AG : ℝ), 1041 ≤ CG → 3 ≤ AG → 1 ≤ Zb D large₂ → 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) := by
  intro D large₂ j ka CG AG hC hA hZ
  have h1 : Zb D large₂ ^ 3 ≤ Zb D large₂ ^ AG := by
    have := Real.rpow_le_rpow_of_exponent_le hZ hA
    rwa [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast] at this
  have h2 : 0 ≤ Real.log ka.size := Real.log_nonneg ka.one_le_size
  have h3 : WeightFamilies.PPv D large₂ CG AG = CG * Zb D large₂ ^ AG := rfl
  have h4 : 0 ≤ Zb D large₂ ^ 3 := by positivity
  rw [h3]
  have h5 : 1041 * Zb D large₂ ^ 3 ≤ CG * Zb D large₂ ^ AG :=
    mul_le_mul hC h1 h4 (by linarith)
  have h6 : 0 ≤ CG * Zb D large₂ ^ AG := le_trans (by positivity) h5
  nlinarith [mul_nonneg h6 h2]

end GlobalTheory
