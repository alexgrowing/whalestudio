import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasFDerivAtOfContinuousCoordinatePartials
import Mathlib
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) → (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | exact GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs <;> assumption)
