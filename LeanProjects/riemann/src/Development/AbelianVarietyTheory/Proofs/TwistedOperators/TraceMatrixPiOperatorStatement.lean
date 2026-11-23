import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMatrixPiOperator
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_sum_single_comp_proj_eq : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  first | exact @GlobalTheory.trace_matrix_pi_operator | exact GlobalTheory.trace_matrix_pi_operator | (intros; apply GlobalTheory.trace_matrix_pi_operator <;> assumption)
