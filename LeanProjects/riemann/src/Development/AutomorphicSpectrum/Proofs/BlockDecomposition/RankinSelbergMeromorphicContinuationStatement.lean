import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_meromorphic_continuation : Ad3.Loc2 → Ad3.R.A10 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 | exact GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.a10 <;> assumption)
