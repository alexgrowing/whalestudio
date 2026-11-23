import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelSummationBound

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abel_summation_bound : ∀ (N : ℕ) (a D : Fin N → ℝ) (Up Lo Cc : ℝ), 0 ≤ Up → 0 ≤ Lo → 0 ≤ Cc → (∀ p q, p ≤ q → a q ≤ a p) → (∀ p, |a p| ≤ 2) → (∀ p : Fin N, (p : ℕ) + 1 < N → -Lo ≤ -∑ k ∈ Finset.Iic p, D k ∧ -∑ k ∈ Finset.Iic p, D k ≤ Up) → (∀ p : Fin N, (p : ℕ) + 1 = N → |∑ k ∈ Finset.Iic p, D k| ≤ Cc) → -(4 * Lo + 2 * Cc) ≤ ∑ p, -a p * D p ∧ ∑ p, -a p * D p ≤ 4 * Up + 2 * Cc := by
  first | exact @GlobalTheory.CompanionTheory.AbelBounds.abel_bound | exact GlobalTheory.CompanionTheory.AbelBounds.abel_bound | (intros; apply GlobalTheory.CompanionTheory.AbelBounds.abel_bound <;> assumption)
