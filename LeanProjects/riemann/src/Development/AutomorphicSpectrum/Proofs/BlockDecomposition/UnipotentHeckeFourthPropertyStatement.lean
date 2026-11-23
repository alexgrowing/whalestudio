import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_hecke_fourth_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.MeasureTransportOpenSet := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | exact GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | (intros; apply GlobalTheory.CompanionTheory.TfLoc.transport_open_trace <;> assumption)
