import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwisted
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.UntwRatS → GlobalTheory.SerStd.SeriesRatS := by
  first | exact @GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | exact GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | (intros; apply GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS <;> assumption)
