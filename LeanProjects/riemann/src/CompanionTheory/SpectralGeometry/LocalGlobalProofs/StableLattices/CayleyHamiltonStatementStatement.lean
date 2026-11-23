import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CayleyHamiltonHk : CompanionTheory.RgExh.Hk.CayleyHam := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | exact GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam <;> assumption)
