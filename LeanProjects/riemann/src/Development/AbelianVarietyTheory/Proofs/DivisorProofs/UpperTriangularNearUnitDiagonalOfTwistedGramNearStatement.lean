import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularNearUnitDiagonalOfTwistedGramNear
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangular_near_unitDiagonal_of_twistedGram_near : ∀ (r : ℕ) (ε : Fin r → ℝ) (b : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), (∀ a, ε a = 1 ∨ ε a = -1) → 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a c : Fin r, ‖(bᵀ * Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) * b.map (starRingEnd ℂ)) a c - Matrix.diagonal (fun a => ((ε a : ℝ) : ℂ)) a c‖ ≤ 3 * δ) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) ∧ ∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ := by
  first | exact @GlobalTheory.upperTriangular_near_diag_of_gram_near | exact GlobalTheory.upperTriangular_near_diag_of_gram_near | (intros; apply GlobalTheory.upperTriangular_near_diag_of_gram_near <;> assumption)
