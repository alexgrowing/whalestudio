import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LeviDecompositionExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomposition_exists : LeviExists := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.leviExists | exact GlobalTheory.CompanionTheory.InertLevi.leviExists | (intros; apply GlobalTheory.CompanionTheory.InertLevi.leviExists <;> assumption)
