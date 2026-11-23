import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformDerivativeApprox
import Mathlib
open Set Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_derivative_approx : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : E × E → E) (U : Set (E × E)), IsOpen U → ContDiffOn ℝ 1 F U → ∀ (K : Set E), IsCompact K → (∀ z ∈ K, (z, (0 : E)) ∈ U) → (∀ z ∈ K, ∀ η : E, HasDerivAt (fun s : ℝ => F (z, s • η)) η 0) → ∀ (ε : ℝ), 0 < ε → ∃ δ > 0, ∃ L : E → E → E →L[ℝ] E, ∀ z ∈ K, ∀ η : E, ‖η‖ ≤ δ → (z, η) ∈ U ∧ HasFDerivAt (fun η' => F (z, η')) (L z η) η ∧ ‖L z η - ContinuousLinearMap.id ℝ E‖ ≤ ε := by
  first | exact @GlobalTheory.fibre_fderiv_uniformly_near_id | exact GlobalTheory.fibre_fderiv_uniformly_near_id | (intros; apply GlobalTheory.fibre_fderiv_uniformly_near_id <;> assumption)
