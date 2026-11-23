import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_restriction_vanishing : PositivityTheory.Rg.BcB.G8.Fin.RestrV := by
  first | exact @GlobalTheory.CompanionTheory.EulerV.main | exact GlobalTheory.CompanionTheory.EulerV.main | (intros; apply GlobalTheory.CompanionTheory.EulerV.main <;> assumption)
