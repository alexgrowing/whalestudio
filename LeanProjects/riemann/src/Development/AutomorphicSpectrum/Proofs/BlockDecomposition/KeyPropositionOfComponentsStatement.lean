import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KeyPropositionOfComponents
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.key_proposition_of_components : PositivityTheory.RgDs.K.LowAlg → PositivityTheory.RgDs.K.HolFacts → PositivityTheory.RgDs.K.EquivSection → PositivityTheory.RgDs.K.RhoRep → PositivityTheory.RgDs.K.ActEquiv → PositivityTheory.RgDs.K.RhoTorus → PositivityTheory.RgDs.K.TorW → PositivityTheory.RgDs.K.Transfer → PositivityTheory.RgDs.K.Exhaust → PositivityTheory.RgDs.K.BetaWeight → PositivityTheory.RgDs.Key := by
  first | exact @GlobalTheory.CompanionTheory.KeyAsm.key_of_steps | exact GlobalTheory.CompanionTheory.KeyAsm.key_of_steps | (intros; apply GlobalTheory.CompanionTheory.KeyAsm.key_of_steps <;> assumption)
