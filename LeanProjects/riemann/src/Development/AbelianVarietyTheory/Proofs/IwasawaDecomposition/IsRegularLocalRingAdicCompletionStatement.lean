import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularLocalRing_adicCompletion' : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  first | exact @GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | exact GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | (intros; apply GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion <;> assumption)
