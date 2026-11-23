import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieve
import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_sq_primitive_char_sum_le : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  first | exact @GlobalTheory.multiplicative_large_sieve | exact GlobalTheory.multiplicative_large_sieve | (intros; apply GlobalTheory.multiplicative_large_sieve <;> assumption)
