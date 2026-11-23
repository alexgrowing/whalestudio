import Formalism.SharpRestriction.Divisibility.WeightAlgebra

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions Formalism.MainNotions

theorem level_bound_of_third_hypothesis {D : D7} {j : ℕ} (large₂ : SizeData₂ D) (H : WeightAlgebra.KHyp) (C2 A2 CR Bx : ℝ)
    (wL : WeightFamilies.Wt D j) (T : ℕ) (h3 : WeightAlgebra.H3 large₂ H C2 A2 CR Bx wL T) (hY : 2 ≤ WeightFamilies.dimY D j)
    (hD : 1 ≤ WeightAlgebra.DF wL) : ∀ i : Fin 2, 4 * WeightAlgebra.DF wL + 4 ≤ D.host.g i := by
  intro i
  have h6 := h3.2.2.2.2.2
  have hq : (WeightAlgebra.qq D : ℝ) ≤ (D.host.g i : ℝ) := by
    have : WeightAlgebra.qq D ≤ D.host.g i := by
      fin_cases i
      · exact min_le_left _ _
      · exact min_le_right _ _
    exact_mod_cast this
  have hY' : (6 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) + 4 := by
    have : (2 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := by exact_mod_cast hY
    linarith
  have hD' : (1 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hD
  have h7 : 6 * (WeightAlgebra.DF wL : ℝ) ≤ ((WeightFamilies.dimY D j : ℝ) + 4) * (WeightAlgebra.DF wL : ℝ) :=
    mul_le_mul_of_nonneg_right hY' (by linarith)
  have h8 : ((4 * WeightAlgebra.DF wL + 4 : ℕ) : ℝ) ≤ (D.host.g i : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h8

end Formalism.MainNotions.ModuliIntegralCharts.H1
