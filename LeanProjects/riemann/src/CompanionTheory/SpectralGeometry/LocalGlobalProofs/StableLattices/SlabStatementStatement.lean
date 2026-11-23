import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SlabStatement : CompanionTheory.RgExh.Dec.N.S.Slab := by
  first | exact @GlobalTheory.CompanionTheory.SlabLemma.slab | exact GlobalTheory.CompanionTheory.SlabLemma.slab | (intros; apply GlobalTheory.CompanionTheory.SlabLemma.slab <;> assumption)
