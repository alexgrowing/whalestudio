import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCommutesSeparableHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_commutes_separable_holds : PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | exact GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | (intros; apply GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable <;> assumption)
