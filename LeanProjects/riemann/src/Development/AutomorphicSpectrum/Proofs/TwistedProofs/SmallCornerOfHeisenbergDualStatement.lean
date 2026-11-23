import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallCornerOfHeisenbergDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_dual : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | exact GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | (intros; apply GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis <;> assumption)
