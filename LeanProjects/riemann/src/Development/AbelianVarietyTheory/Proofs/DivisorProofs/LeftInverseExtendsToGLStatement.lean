import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseExtendsToGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_inverse_extends_to_GL : ∀ (K : Type) [Field K] (n r : ℕ) (X : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), L * X = 1 →
    r ≤ n ∧ ∃ C : GL (Fin n) K, ∀ (j : Fin r) (k : Fin n), (k : ℕ) = j → (∀ a, C.1 a k = X a j) ∧ ∀ a, (C⁻¹).1 k a = L j a := by
  first | exact @GlobalTheory.exists_GL_cols_eq_inv_rows_eq_of_mul_eq_one | exact GlobalTheory.exists_GL_cols_eq_inv_rows_eq_of_mul_eq_one | (intros; apply GlobalTheory.exists_GL_cols_eq_inv_rows_eq_of_mul_eq_one <;> assumption)
