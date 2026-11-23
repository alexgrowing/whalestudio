import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_rankin_selberg_basic_facts : Ad3.R.B0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinQ.b0 | exact GlobalTheory.CompanionTheory.RankinQ.b0 | (intros; apply GlobalTheory.CompanionTheory.RankinQ.b0 <;> assumption)
