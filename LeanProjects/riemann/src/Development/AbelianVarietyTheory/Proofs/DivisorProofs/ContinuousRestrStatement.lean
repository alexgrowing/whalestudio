import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_afP_restr : ∀ (p : ℕ), Continuous (GlobalTheory.LKTrip.AfP.restr p) := by
  first | (exact @GlobalTheory.LKTrip.AfP.continuous_restr) | (exact GlobalTheory.LKTrip.AfP.continuous_restr) | (intros; apply GlobalTheory.LKTrip.AfP.continuous_restr  <;> assumption)
