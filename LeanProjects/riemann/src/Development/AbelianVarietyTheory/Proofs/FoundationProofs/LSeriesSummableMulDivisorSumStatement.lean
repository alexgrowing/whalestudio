import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableMulDivisorSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpowStatement
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lSeriesSummable_mul_divisorSum' : ∀ (e : ℕ) (ψ θ g b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n : ℕ => g n * b n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.DivConvSum.lSeriesSummable_mul_divisorSum | exact GlobalTheory.DivConvSum.lSeriesSummable_mul_divisorSum | (intros; apply GlobalTheory.DivConvSum.lSeriesSummable_mul_divisorSum <;> assumption)
