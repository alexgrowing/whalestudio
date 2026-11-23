import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueeze
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_small_ball_density_of_squeeze : ∀ (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal), v ≠ ⊤ → (∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal, Filter.Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) ∧ ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧ f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) → Filter.Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) := by
  first | exact @GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | exact GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | (intros; apply GlobalTheory.IwConst.tendsto_div_pow_of_squeeze <;> assumption)
