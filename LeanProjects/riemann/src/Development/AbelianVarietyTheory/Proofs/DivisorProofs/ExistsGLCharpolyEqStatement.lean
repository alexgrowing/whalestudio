import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_charpoly_eq_of_mem_Ell : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  first | exact @GlobalTheory.CompanionEll.exists_GL_charpoly_eq | exact GlobalTheory.CompanionEll.exists_GL_charpoly_eq | (intros; apply GlobalTheory.CompanionEll.exists_GL_charpoly_eq <;> assumption)
