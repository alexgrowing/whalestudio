import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFacts
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rgExh_lineFacts : CompanionTheory.RgExh.Dec.N.S.LineFacts := by
  first | exact @GlobalTheory.CompanionTheory.GradLine.lineFacts | exact GlobalTheory.CompanionTheory.GradLine.lineFacts | (intros; apply GlobalTheory.CompanionTheory.GradLine.lineFacts <;> assumption)
