import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryBlockDiagonalLeviElement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_block_diagonal_levi_element : LeviExists := by
  first | exact @GlobalTheory.InertZeta.leviExists | exact GlobalTheory.InertZeta.leviExists | (intros; apply GlobalTheory.InertZeta.leviExists <;> assumption)
