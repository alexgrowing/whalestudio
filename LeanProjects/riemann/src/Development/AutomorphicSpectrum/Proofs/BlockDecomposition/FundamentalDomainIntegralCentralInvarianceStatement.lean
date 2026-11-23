import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_integral_central_invariance : Ad3.R.G1a := by
  first | exact @GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | exact GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | (intros; apply GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts <;> assumption)
