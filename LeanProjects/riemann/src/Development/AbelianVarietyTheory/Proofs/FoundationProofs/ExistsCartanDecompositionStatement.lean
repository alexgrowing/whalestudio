import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCartanDecomposition
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartan_decomposition : ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), IsInU ε g → ∃ X, IsCartan ε g X := by
  first | exact @GlobalTheory.CartanExists.exists_isCartan | exact GlobalTheory.CartanExists.exists_isCartan | (intros; apply GlobalTheory.CartanExists.exists_isCartan <;> assumption)
