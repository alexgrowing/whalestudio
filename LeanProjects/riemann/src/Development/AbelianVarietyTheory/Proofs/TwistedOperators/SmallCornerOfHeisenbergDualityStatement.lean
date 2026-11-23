import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallCornerOfHeisenbergDuality
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_duality : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.InertZeta.smallCorner_of_heis_dual | exact GlobalTheory.InertZeta.smallCorner_of_heis_dual | (intros; apply GlobalTheory.InertZeta.smallCorner_of_heis_dual <;> assumption)
