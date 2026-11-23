import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommuting
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_norm_commuting : PositivityTheory.Rg.Tf.Loc.A1 := by
  first | exact @GlobalTheory.CompanionTheory.Centraliser.a1 | exact GlobalTheory.CompanionTheory.Centraliser.a1 | (intros; apply GlobalTheory.CompanionTheory.Centraliser.a1 <;> assumption)
