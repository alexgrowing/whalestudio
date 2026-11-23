import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonScalar
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeNonScalar : CompanionTheory.RgExh.Hk.NonScal := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal | exact GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal <;> assumption)
