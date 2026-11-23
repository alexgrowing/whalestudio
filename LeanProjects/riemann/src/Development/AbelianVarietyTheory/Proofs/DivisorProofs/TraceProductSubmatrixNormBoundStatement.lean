import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceProductSubmatrixNormBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_product_submatrix_norm_bound : ∀ {m : ℕ} (k : Fin (m + 1)) (P : Matrix (Fin k) (Fin k) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) (b g : ℝ), 0 ≤ b → 0 ≤ g → (∀ y, ‖P *ᵥ y‖ ≤ b * ‖y‖) → (∀ x, ‖X *ᵥ x‖ ≤ g * ‖x‖) → ‖(P * X.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).trace‖ ≤ m * (b * g) := by
  first | exact @GlobalTheory.trace_mul_submatrix_norm_le | exact GlobalTheory.trace_mul_submatrix_norm_le | (intros; apply GlobalTheory.trace_mul_submatrix_norm_le <;> assumption)
