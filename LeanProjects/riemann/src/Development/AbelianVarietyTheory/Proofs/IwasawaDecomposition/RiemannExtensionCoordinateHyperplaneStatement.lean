import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplane
import Mathlib
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  first | exact @GlobalTheory.riemann_extension_coordinate_hyperplane | exact GlobalTheory.riemann_extension_coordinate_hyperplane | (intros; apply GlobalTheory.riemann_extension_coordinate_hyperplane <;> assumption)
