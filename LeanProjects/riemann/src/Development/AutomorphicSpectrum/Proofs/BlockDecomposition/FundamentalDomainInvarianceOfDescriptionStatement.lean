import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_invariance_of_description : Ad3.R.D0 → Ad3.R.G0 := by
  first | exact @GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | exact GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | (intros; apply GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain <;> assumption)
