import Formalism.SizeWindowBrackets.PowerBoundGivesRiemannHypothesis
import Formalism.ZetaNonvanishing.ZetaLandau
import Formalism.ZetaNonvanishing.RHofHalfPlane

namespace Formalism.LFunctionChainParameters.ConditionalMainTheorem

open Formalism

theorem landau_zero_free_half_plane : LandauZeroFreeHalfPlane := by
  intro θ h0 h1 y₀ hG s hs
  exact Formalism.zetaLandau 1 (Or.inl rfl) θ h0 h1 ⟨1, y₀, fun y hy => by simpa using hG y hy⟩ s hs

theorem riemann_hypothesis_of_power_bound : PowerBoundGivesRiemannHypothesis := by
  intro C ε₁ hε₁ hG
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  intro s hs
  refine Formalism.zetaLandauEps 1 (Or.inl rfl) (1 / 2) (by norm_num) (by norm_num) ?_ s hs
  intro ε' hε'
  set ε : ℝ := min (ε₁ / 2) (ε' / (|C| + 1)) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (div_pos hε' (by positivity))
  have hεlt : ε < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨x₀, hx⟩ := hG ε hε0 hεlt
  refine ⟨1, max x₀ 1, fun x hx' => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx'
  have hCe : C * ε ≤ ε' := by
    have h1 : C * ε ≤ |C| * ε := mul_le_mul_of_nonneg_right (le_abs_self C) hε0.le
    have h2 : ε ≤ ε' / (|C| + 1) := min_le_right _ _
    have h3 : |C| * ε ≤ (|C| + 1) * ε := by nlinarith [abs_nonneg C]
    have h4 : (|C| + 1) * ε ≤ ε' := by
      rw [le_div_iff₀ (by positivity)] at h2; linarith
    linarith
  have := hx x (le_trans (le_max_left _ _) hx')
  calc (1 : ℝ) * Gz x = Gz x := one_mul _
    _ ≤ x ^ (1 / 2 + C * ε) := this
    _ ≤ x ^ (1 / 2 + ε') := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = 1 * x ^ (1 / 2 + ε') := (one_mul _).symm

end Formalism.LFunctionChainParameters.ConditionalMainTheorem
