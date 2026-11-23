import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRiemannZetaSubPartialSumLe
import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_riemannZeta_sub_partial_sum_le : ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M → ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖ ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  first | exact @GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | exact GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | (intros; apply GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le <;> assumption)
