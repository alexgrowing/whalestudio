import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)), ϖ ≠ 0 → (∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) → ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first | exact @GlobalTheory.exists_square_matrix_of_submodule_between | exact GlobalTheory.exists_square_matrix_of_submodule_between | (intros; apply GlobalTheory.exists_square_matrix_of_submodule_between <;> assumption)
