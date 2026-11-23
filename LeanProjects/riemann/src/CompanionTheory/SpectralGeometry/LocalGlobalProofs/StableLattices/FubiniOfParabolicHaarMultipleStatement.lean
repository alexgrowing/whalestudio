import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniOfParabolicHaarMultiple
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_of_parabolic_haar_multiple : CompanionTheory.RgExh.Dec.N.S.Fub2 → CompanionTheory.RgExh.Dec.N.S.Fub := by
  first | exact @GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple | exact GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple | (intros; apply GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple <;> assumption)
