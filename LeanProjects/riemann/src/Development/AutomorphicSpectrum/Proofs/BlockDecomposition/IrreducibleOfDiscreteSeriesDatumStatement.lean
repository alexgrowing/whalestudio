import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleOfDiscreteSeriesDatum
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepIrred := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | exact GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum <;> assumption)
