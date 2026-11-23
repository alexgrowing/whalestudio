import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsGLConjEqDiagonalOfCharpolyEqProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalize_of_distinct_eigenvalues : ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C), (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) → ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  first | exact @GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod | exact GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod | (intros; apply GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod <;> assumption)
