import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMain
import Formalism.GL3MeanSquares.PrimePairOfBoxAndWeakMeanSquareHypotheses

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem mean_square_of_pnt_progressions (hP : PNTAPRelW) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, 0 < C ∧ Formalism.HermitianLattices.WeakMeanSquareEstimates.MeanSquareHypW ε C x₀ := by
  intro ε hε hε1
  obtain ⟨C, x₀, h⟩ := meanSquareHypW_of_pnt hP ε hε hε1
  refine ⟨max C 1, max x₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro x X m₀ a₀ κ hx h8 hp ha h4 h1 h2 h3 hk hm
  obtain ⟨ha', hb⟩ := h x X m₀ a₀ κ (le_trans (le_max_left _ _) hx) h8 hp ha h4 h1 h2 h3 hk hm
  refine ⟨ha', le_trans hb ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hc : (0 : ℝ) ≤ ((Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ X).card : ℝ) := Nat.cast_nonneg _
  have hxl : 0 ≤ x * Real.log x * ((Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ X).card : ℝ) :=
    mul_nonneg (mul_nonneg (by linarith) hl) hc
  have := mul_le_mul_of_nonneg_right (le_max_left C 1) hxl
  simpa [mul_assoc] using this

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
