import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantGLOfUpperTriangularRightInvariant
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant : ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k), (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) → (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) → (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id → ψ (A * T) = ψ A) → ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  first | exact @GlobalTheory.rightInv_of_upperTriangular_rightInv | exact GlobalTheory.rightInv_of_upperTriangular_rightInv | (intros; apply GlobalTheory.rightInv_of_upperTriangular_rightInv <;> assumption)
