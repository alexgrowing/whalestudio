import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeSecond
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.NilpotentOdeSecond : CompanionTheory.RgExh.Dec.N.OdeB := by
  first | exact @GlobalTheory.CompanionTheory.OdeRoots.Above.odeB | exact GlobalTheory.CompanionTheory.OdeRoots.Above.odeB | (intros; apply GlobalTheory.CompanionTheory.OdeRoots.Above.odeB <;> assumption)
