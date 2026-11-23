import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeometricStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.GeometricStatement : CompanionTheory.RgExh.Dec.L.Geo := by
  first | exact @GlobalTheory.CompanionTheory.UGeo.geo | exact GlobalTheory.CompanionTheory.UGeo.geo | (intros; apply GlobalTheory.CompanionTheory.UGeo.geo <;> assumption)
