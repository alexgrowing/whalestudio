import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDotProductMulVecEqOfLinearIndependent
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_mulVec_eq_of_linearIndependent' : ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 → LinearIndependent ℚ ε → ∀ t : Fin k → ℚ, ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  first | exact @GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | exact GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | (intros; apply GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent <;> assumption)
