import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeFirst
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.NilpotentOdeFirst : CompanionTheory.RgExh.Dec.N.OdeA := by
  first | exact @GlobalTheory.CompanionTheory.OdeRoots.odeA | exact GlobalTheory.CompanionTheory.OdeRoots.odeA | (intros; apply GlobalTheory.CompanionTheory.OdeRoots.odeA <;> assumption)
