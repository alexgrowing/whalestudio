import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStable
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeBackwardStable : CompanionTheory.RgExh.Hk.BackStable := by
  first | exact @GlobalTheory.CompanionTheory.RgHeckeBack.backStable | exact GlobalTheory.CompanionTheory.RgHeckeBack.backStable | (intros; apply GlobalTheory.CompanionTheory.RgHeckeBack.backStable <;> assumption)
