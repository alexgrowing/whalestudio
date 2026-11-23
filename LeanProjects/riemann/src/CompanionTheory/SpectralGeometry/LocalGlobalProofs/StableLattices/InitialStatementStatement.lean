import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.InitialStatement : CompanionTheory.RgExh.Dec.N.S.StartOf := by
  first | exact @GlobalTheory.CompanionTheory.RgStart.startOf | exact GlobalTheory.CompanionTheory.RgStart.startOf | (intros; apply GlobalTheory.CompanionTheory.RgStart.startOf <;> assumption)
