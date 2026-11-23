import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtZeroEqSumIntegralKernelIteratedDeriv
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernels_eval_zero_eq_sum_integral_iteratedDeriv : ∀ ε : ℝ, 0 < ε → ∃ κ : Fin 3 → ℝ → ℂ, (∀ n, Continuous (κ n) ∧ tsupport (κ n) ⊆ Set.Icc (-ε) ε) ∧ ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → u 0 = ∑ n : Fin 3, ∫ t, κ n t * iteratedDeriv n u t := by
  first | exact @GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv | exact GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv | (intros; apply GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv <;> assumption)
