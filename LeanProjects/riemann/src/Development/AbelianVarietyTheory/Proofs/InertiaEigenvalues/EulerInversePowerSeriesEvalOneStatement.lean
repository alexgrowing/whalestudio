import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerInverse_powerSeries_eval_one : ∀ {ι : Type} [Fintype ι] (c : ℕ → ℂ), (Summable fun d => ‖c d‖) → ∀ (Q : ι → ℂ),
    PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1 →
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  first | exact @GlobalTheory.JSW.eulerInverse_eval_one | exact GlobalTheory.JSW.eulerInverse_eval_one | (intros; apply GlobalTheory.JSW.eulerInverse_eval_one <;> assumption)
