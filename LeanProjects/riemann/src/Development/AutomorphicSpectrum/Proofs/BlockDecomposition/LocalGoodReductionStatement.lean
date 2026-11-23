import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReduction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_good_reduction : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  first | exact @GlobalTheory.CompanionTheory.LocGoodProof.locGood | exact GlobalTheory.CompanionTheory.LocGoodProof.locGood | (intros; apply GlobalTheory.CompanionTheory.LocGoodProof.locGood <;> assumption)
