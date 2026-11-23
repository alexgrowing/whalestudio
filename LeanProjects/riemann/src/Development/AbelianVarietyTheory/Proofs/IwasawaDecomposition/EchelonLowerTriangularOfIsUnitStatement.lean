import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EchelonLowerTriangularOfIsUnit
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.echelon_lower_triangular_of_isUnit : ∀ {K : Type} [Field K] (m : ℕ) (M : Matrix (Fin m) (Fin m) K), IsUnit M → ∃ (g : Matrix (Fin m) (Fin m) K) (s : Fin (m.choose 2) → K), IsUnit g ∧ g.transpose.BlockTriangular id ∧ ∀ i j, (g * M) i j = 0 ∨ (g * M) i j = 1 ∨ (g * M) i j ∈ Set.range s := by
  first | exact @GlobalTheory.echelon_lowerTriangular | exact GlobalTheory.echelon_lowerTriangular | (intros; apply GlobalTheory.echelon_lowerTriangular <;> assumption)
