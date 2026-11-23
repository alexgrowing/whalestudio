import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfIntegralMatrixUltrametric
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K), (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K), c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 := by
  first | exact @GlobalTheory.eigenvalue_integral_matrix_norm_le_one | exact GlobalTheory.eigenvalue_integral_matrix_norm_le_one | (intros; apply GlobalTheory.eigenvalue_integral_matrix_norm_le_one <;> assumption)
