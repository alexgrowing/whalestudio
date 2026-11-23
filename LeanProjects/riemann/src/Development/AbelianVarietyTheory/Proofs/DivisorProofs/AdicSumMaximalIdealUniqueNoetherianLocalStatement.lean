import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
open IsLocalRing GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicSum_maximalIdeal_unique_noetherian_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (Ix : Type) (x : Ix → R) (s s' : R), SumI (maximalIdeal R) x s → SumI (maximalIdeal R) x s' → s = s' := by
  first | exact @GlobalTheory.Poinc.sumI_maximalIdeal_unique | exact GlobalTheory.Poinc.sumI_maximalIdeal_unique | (intros; apply GlobalTheory.Poinc.sumI_maximalIdeal_unique <;> assumption)
