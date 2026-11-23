import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPath
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PolynomialNilpotentPath : CompanionTheory.RgExh.Dec.L.PolyNilPath := by
  first | exact @GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath | exact GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath | (intros; apply GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath <;> assumption)
