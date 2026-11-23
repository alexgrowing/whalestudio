import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralCoeffInterpolationBivariateSeries
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coeff_interpolation_bivariate_series : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (S : Finset K) (H : MvPowerSeries (Fin 2) K), (∀ x ∈ S, ‖x‖ < 1) → Intg H → ∃ c : Fin S.card → Fin S.card → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ x ∈ S, ∀ y ∈ S, ev H ![x, y] = ∑ a, ∑ b, c a b * x ^ (a : ℕ) * y ^ (b : ℕ) := by
  first | exact @GlobalTheory.ConvSer.exists_integral_interpolation_two | exact GlobalTheory.ConvSer.exists_integral_interpolation_two | (intros; apply GlobalTheory.ConvSer.exists_integral_interpolation_two <;> assumption)
