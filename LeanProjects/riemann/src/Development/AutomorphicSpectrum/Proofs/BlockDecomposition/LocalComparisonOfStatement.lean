import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  first | exact @GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | exact GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | (intros; apply GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf <;> assumption)
