import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitDetAddMulOfFromBlocksLocalRing
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | exact GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | (intros; apply GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul <;> assumption)
