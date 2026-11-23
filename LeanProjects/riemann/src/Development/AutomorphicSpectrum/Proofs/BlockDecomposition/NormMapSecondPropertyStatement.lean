import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_second_property : PositivityTheory.Rg.Tf.Loc.N2 := by
  first | exact @GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | exact GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | (intros; apply GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder <;> assumption)
