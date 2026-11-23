import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatAlternatingOrthogonalOrthogonalLeAlt
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_orthogonal_orthogonal_of_skew_det_ne_zero : ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq → Mq.det ≠ 0 → ∀ x : Fin r → ℚ, (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  first | exact @GlobalTheory.rat_alternating_orthogonal_orthogonal_le | exact GlobalTheory.rat_alternating_orthogonal_orthogonal_le | (intros; apply GlobalTheory.rat_alternating_orthogonal_orthogonal_le <;> assumption)
