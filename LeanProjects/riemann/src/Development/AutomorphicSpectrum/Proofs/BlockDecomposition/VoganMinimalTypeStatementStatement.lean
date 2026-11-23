import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatement
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vogan_minimal_type_statement : PositivityTheory.RgDs.Hilb.StepVogan := by
  first | exact @GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | exact GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | (intros; apply GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan <;> assumption)
