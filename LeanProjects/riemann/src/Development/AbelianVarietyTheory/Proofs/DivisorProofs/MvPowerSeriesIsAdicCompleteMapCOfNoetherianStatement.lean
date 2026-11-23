import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  first | exact @GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | exact GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | (intros; apply GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C <;> assumption)
