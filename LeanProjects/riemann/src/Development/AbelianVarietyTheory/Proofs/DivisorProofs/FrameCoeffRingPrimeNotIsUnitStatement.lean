import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameCoeffRing_prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.prime_not_isUnit | exact GlobalTheory.ExpFrame.Frame.prime_not_isUnit | (intros; apply GlobalTheory.ExpFrame.Frame.prime_not_isUnit <;> assumption)
