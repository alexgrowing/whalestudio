import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_weierstrass_chart_xy_unit_series : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧), M.Chart ℓ → coeff 1 ℓ ≠ 0 ∧ ∃ v xs ys : ℂ_[q]⟦X⟧, Bd 1 v ∧ Bd 1 xs ∧ Bd 1 ys ∧ ‖constantCoeff v‖ = 1 ∧ ‖constantCoeff xs‖ = 1 ∧ ‖constantCoeff ys‖ = 1 ∧ hat M.ι ℓ M.u = X * v ∧ hat M.ι ℓ M.w * ys = -X ^ 3 ∧ xs = -v * ys ∧ ∀ (F : ℂ → ℂ) (A B : Polynomial ℂ) (k : ℕ), AnalyticAt ℂ F 0 → A.natDegree ≤ k → B.natDegree ≤ k → ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → ∀ (D : Polynomial ℂ) (j : ℕ), D.natDegree ≤ j → (∀ᶠ z in 𝓝[≠] (0 : ℂ), F z * D.eval (M.x z) = G z * (A.eval (M.x z) + B.eval (M.x z) * M.y z)) → hat M.ι ℓ F * X ^ (2 * k + 3) * (∑ i ∈ Finset.range (j + 1), C (M.ι (D.coeff i)) * X ^ (2 * (j - i)) * xs ^ i) = hat M.ι ℓ G * X ^ (2 * j) * ∑ i ∈ Finset.range (k + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i + C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
  first | exact @GlobalTheory.MomOne.ChartXY.chart_xy | exact GlobalTheory.MomOne.ChartXY.chart_xy | (intros; apply GlobalTheory.MomOne.ChartXY.chart_xy <;> assumption)
