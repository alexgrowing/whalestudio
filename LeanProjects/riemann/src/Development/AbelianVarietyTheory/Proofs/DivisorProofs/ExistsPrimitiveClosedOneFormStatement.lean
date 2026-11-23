import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveClosedOneForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_closed_one_form : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {U : Set V} (w₁ : V → V →L[ℝ] ℂ), IsOpen U → SimplyConnectedSpace U → ContDiffOn ℝ 1 w₁ U → (∀ a ∈ U, ∀ x y : V, fderiv ℝ w₁ a x y = fderiv ℝ w₁ a y x) → ∃ F : V → ℂ, ∀ a ∈ U, HasFDerivAt F (w₁ a) a := by
  first | exact @GlobalTheory.PrimLift.exists_primitive_of_simplyConnected | exact GlobalTheory.PrimLift.exists_primitive_of_simplyConnected | (intros; apply GlobalTheory.PrimLift.exists_primitive_of_simplyConnected <;> assumption)
