import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ), (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) → (∀ i, Continuous (d i)) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_partials | exact GlobalTheory.hasFDerivAt_of_continuous_partials | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_partials <;> assumption)
