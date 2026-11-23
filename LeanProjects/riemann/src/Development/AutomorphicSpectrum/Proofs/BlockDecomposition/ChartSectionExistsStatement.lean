import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_section_exists : TChart := by
  first | exact @GlobalTheory.CompanionTheory.TChartProof.tChart | exact GlobalTheory.CompanionTheory.TChartProof.tChart | (intros; apply GlobalTheory.CompanionTheory.TChartProof.tChart <;> assumption)
