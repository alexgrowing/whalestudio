import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFrameCoeffRingQuotientPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_frameCoeffRing_quotient_prime : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  first | exact @GlobalTheory.FrameQuot.finite_quot_prime | exact GlobalTheory.FrameQuot.finite_quot_prime | (intros; apply GlobalTheory.FrameQuot.finite_quot_prime <;> assumption)
