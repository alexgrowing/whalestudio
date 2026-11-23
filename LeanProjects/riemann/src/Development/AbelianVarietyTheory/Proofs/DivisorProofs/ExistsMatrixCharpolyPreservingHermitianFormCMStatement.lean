import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCM
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_charpoly_preserving_hermitian_form_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  first | exact @GlobalTheory.GlobHerm.exists_mat_herm | exact GlobalTheory.GlobHerm.exists_mat_herm | (intros; apply GlobalTheory.GlobHerm.exists_mat_herm <;> assumption)
