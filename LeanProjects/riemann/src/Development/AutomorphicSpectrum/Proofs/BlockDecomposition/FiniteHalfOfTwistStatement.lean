import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwist
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_half_of_twist : PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf := by
  first | exact @GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | exact GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | (intros; apply GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf <;> assumption)
