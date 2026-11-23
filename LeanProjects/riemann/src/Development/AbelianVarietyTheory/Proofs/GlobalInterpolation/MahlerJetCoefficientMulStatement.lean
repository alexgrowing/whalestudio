import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMul
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahlerJetCoefficient_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ : Type) [Fintype κ] [DecidableEq κ] (v : κ → V) (F G : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ G → ∀ n : κ → ℕ, mahler v (fun z => F z * G z) n = ∑ k ∈ Fintype.piFinset (fun i => Finset.range (n i + 1)), mahler v F k * mahler v G (fun i => n i - k i) := by
  first | exact @GlobalTheory.MomN.mahler_mul | exact GlobalTheory.MomN.mahler_mul | (intros; apply GlobalTheory.MomN.mahler_mul <;> assumption)
