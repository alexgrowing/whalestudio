import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixFamilyCriticalRows
import Mathlib
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_family_critical_rows : ∀ (p q : ℕ) (ι : Type) [Countable ι] (r : ℝ) (_ : 0 < r) (z₀ w : Matrix (Fin p) (Fin q) ℂ) (M : ι → ℂ → Matrix (Fin p) (Fin p ⊕ Fin q) ℂ), (∀ i a b, DifferentiableOn ℂ (fun t => M i t a b) (Metric.ball 0 r)) → (∀ i a b, deriv (fun t => M i t a b) 0 = 0) → (∀ t ∈ Metric.ball (0 : ℂ) r, ∃ i, M i t * Matrix.fromRows (z₀ + t • w) (1 : Matrix (Fin q) (Fin q) ℂ) = 0) → (∀ i, ∃ R : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ, M i 0 * R = 1) → w = 0 := by
  first | exact @GlobalTheory.eq_zero_of_family_killing_graph | exact GlobalTheory.eq_zero_of_family_killing_graph | (intros; apply GlobalTheory.eq_zero_of_family_killing_graph <;> assumption)
