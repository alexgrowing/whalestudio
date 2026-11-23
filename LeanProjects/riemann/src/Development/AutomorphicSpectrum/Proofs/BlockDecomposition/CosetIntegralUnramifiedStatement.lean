import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIntegralUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_integral_unramified : PositivityTheory.SiegelWeilFormula.Gunr.CosetInt := by
  first | exact @GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | exact GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | (intros; apply GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq <;> assumption)
