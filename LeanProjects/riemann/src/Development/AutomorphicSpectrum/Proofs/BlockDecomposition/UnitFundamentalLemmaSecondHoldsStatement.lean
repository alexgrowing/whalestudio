import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaSecondHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_fundamental_lemma_second_holds : PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.Z2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second <;> assumption)
