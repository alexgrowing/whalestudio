import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZeros
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K), Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ ev1 h x = 0) → (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card, ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  first | exact @GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | exact GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | (intros; apply GlobalTheory.ConvSer.norm_coeff_le_prod_zeros <;> assumption)
