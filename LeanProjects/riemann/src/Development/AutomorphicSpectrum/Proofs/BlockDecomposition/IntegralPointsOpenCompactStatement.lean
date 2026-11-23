import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompact
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kernel_compact_open : PositivityTheory.Rg.BcB.G8.KfOC := by
  first | exact @GlobalTheory.CompanionTheory.IntegralPoints.kfOC | exact GlobalTheory.CompanionTheory.IntegralPoints.kfOC | (intros; apply GlobalTheory.CompanionTheory.IntegralPoints.kfOC <;> assumption)
