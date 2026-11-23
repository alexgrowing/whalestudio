import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_section_exists : TStd := by
  first | exact @GlobalTheory.CompanionTheory.StdChart.tStd | exact GlobalTheory.CompanionTheory.StdChart.tStd | (intros; apply GlobalTheory.CompanionTheory.StdChart.tStd <;> assumption)
