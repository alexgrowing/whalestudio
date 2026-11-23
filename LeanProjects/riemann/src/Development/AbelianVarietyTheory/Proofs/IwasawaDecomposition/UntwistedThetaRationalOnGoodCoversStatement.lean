import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedThetaRationalOnGoodCovers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_theta_rational_on_good_covers : GlobalTheory.SerStd.UntwRatS := by
  first | exact @GlobalTheory.SerStd.untwRatS | exact GlobalTheory.SerStd.untwRatS | (intros; apply GlobalTheory.SerStd.untwRatS <;> assumption)
