import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_fundamental_lemma_first_holds : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.L3 → PositivityTheory.Rg.Tf.Loc.L4 → PositivityTheory.Rg.Tf.Loc.H2 → PositivityTheory.Rg.Tf.Loc.H3 → PositivityTheory.Rg.Tf.Loc.H4 → PositivityTheory.Rg.Tf.Loc.Z1 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first <;> assumption)
