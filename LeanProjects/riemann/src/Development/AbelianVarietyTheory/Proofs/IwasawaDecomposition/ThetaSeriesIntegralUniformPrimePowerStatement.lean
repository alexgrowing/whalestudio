import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesIntegralUniformPrimePower
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integral_uniform_prime_power : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  first | exact @GlobalTheory.serInt_outright | exact GlobalTheory.serInt_outright | (intros; apply GlobalTheory.serInt_outright <;> assumption)
