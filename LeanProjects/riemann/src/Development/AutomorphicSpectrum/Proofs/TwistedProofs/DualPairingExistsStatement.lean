import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_pairing_exists : Dual := by
  first | exact @GlobalTheory.CompanionTheory.InertDual.dual | exact GlobalTheory.CompanionTheory.InertDual.dual | (intros; apply GlobalTheory.CompanionTheory.InertDual.dual <;> assumption)
