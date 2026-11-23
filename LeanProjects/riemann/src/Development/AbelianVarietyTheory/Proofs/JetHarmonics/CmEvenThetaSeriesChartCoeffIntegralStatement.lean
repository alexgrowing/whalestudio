import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegral
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_even_theta_series_chart_coeff_integral : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → Bd 1 (hat M.ι (C ω * logS) θ) := by
  first | exact @GlobalTheory.MomOne.theta_series_integral | exact GlobalTheory.MomOne.theta_series_integral | (intros; apply GlobalTheory.MomOne.theta_series_integral <;> assumption)
