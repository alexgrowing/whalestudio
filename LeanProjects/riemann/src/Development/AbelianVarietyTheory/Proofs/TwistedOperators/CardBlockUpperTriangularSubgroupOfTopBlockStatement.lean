import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardBlockUpperTriangularSubgroupOfTopBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockPartitionOfEqTwoBlock
open Matrix Formalism.L2.DIV GlobalTheory.ParIndex

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_blockUpperTriangularSubgroupOfTopBlock : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ) (hr : r ≤ n), n = r + t → ∀ H : Subgroup (GL (Fin r) κ), Nat.card (GlobalTheory.ParIndex.parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  first | exact @GlobalTheory.ParIndex.card_parSub | exact GlobalTheory.ParIndex.card_parSub | (intros; apply GlobalTheory.ParIndex.card_parSub <;> assumption)
