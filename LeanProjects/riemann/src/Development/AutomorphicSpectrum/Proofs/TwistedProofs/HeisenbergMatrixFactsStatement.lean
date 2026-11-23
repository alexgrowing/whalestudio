import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.HeisenbergMatrixFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_matrix_facts : Heis := by
  first | exact @GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | exact GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | (intros; apply GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ <;> assumption)
