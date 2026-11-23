import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterFormulaOfDiscreteSeriesDatum
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_formula_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepFormulaF := by
  first | exact @GlobalTheory.CompanionTheory.Hilb.stepFormulaF | exact GlobalTheory.CompanionTheory.Hilb.stepFormulaF | (intros; apply GlobalTheory.CompanionTheory.Hilb.stepFormulaF <;> assumption)
