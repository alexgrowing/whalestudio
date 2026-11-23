import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_of_heisenberg_index : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.CompanionTheory.InertCount.count | exact GlobalTheory.CompanionTheory.InertCount.count | (intros; apply GlobalTheory.CompanionTheory.InertCount.count <;> assumption)
