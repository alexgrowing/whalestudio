import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidef
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef : ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef → 0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  first | exact @GlobalTheory.sum_hadamard_posDef_posSemidef | exact GlobalTheory.sum_hadamard_posDef_posSemidef | (intros; apply GlobalTheory.sum_hadamard_posDef_posSemidef <;> assumption)
