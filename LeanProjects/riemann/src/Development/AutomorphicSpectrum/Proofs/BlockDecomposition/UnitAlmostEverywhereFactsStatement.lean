import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitAlmostEverywhereFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_almost_everywhere_facts : PositivityTheory.Rg.BcB.G8.Fin.UnitAE := by
  first | exact @GlobalTheory.CompanionTheory.UnitAEPair.main | exact GlobalTheory.CompanionTheory.UnitAEPair.main | (intros; apply GlobalTheory.CompanionTheory.UnitAEPair.main <;> assumption)
