import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeAlgebraFacts
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_degree_algebra_facts : PositivityTheory.RgDs.K.LowAlg := by
  first | exact @GlobalTheory.CompanionTheory.GlLowest.lowAlg | exact GlobalTheory.CompanionTheory.GlLowest.lowAlg | (intros; apply GlobalTheory.CompanionTheory.GlLowest.lowAlg <;> assumption)
