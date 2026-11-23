import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDefiniteLeadingMinorInverseBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_definite_leading_minor_inverse_bound : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : Fin (m + 1)) (c : ℝ), 0 < c → IsUnit (M.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det → (∀ v : Fin m → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ M *ᵥ v).re) → ∀ z : Fin k → ℂ, ‖(M.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt)))⁻¹ *ᵥ z‖ ≤ m / c * ‖z‖ := by
  first | exact @GlobalTheory.leadingBlock_inv_mulVec_norm_le | exact GlobalTheory.leadingBlock_inv_mulVec_norm_le | (intros; apply GlobalTheory.leadingBlock_inv_mulVec_norm_le <;> assumption)
