import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergTheorem
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_theorem : Ad3.R.B0 → Ad3.R.F0 → Ad3.R.F1 → Ad3.R.F7 → Ad3.R.X1 → Ad3.RS := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergTop.rs_of | exact GlobalTheory.CompanionTheory.RankinSelbergTop.rs_of | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergTop.rs_of <;> assumption)
