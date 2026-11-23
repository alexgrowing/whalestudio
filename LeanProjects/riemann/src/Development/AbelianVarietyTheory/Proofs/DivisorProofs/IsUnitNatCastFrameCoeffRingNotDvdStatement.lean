import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastFrameCoeffRingNotDvd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok → ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd | exact GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd | (intros; apply GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd <;> assumption)
