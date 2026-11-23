import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredBound
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_log_prime_div_pred_bound : ∀ (B : ℕ) (bad S : Finset ℕ), 128 ≤ B → bad.card ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ bad)) → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB | exact GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB <;> assumption)
