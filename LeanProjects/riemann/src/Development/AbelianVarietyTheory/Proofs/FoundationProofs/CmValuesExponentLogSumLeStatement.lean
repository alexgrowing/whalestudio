import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesExponentLogSumLe
import Formalism.PairingDivisors.StatementN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmValues_exponent_log_sum_le : Formalism.PairingDivisionLocalBalance.CESum := by
  first | exact @GlobalTheory.dividedPowerValuations_cESum | exact GlobalTheory.dividedPowerValuations_cESum | (intros; apply GlobalTheory.dividedPowerValuations_cESum <;> assumption)
