import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ), ∃ Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ IsCompact (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ intMat a b w = AddSubgroup.toSubgroup Λ := by
  first | exact @GlobalTheory.IntMatOpen.intMat_open_compact | exact GlobalTheory.IntMatOpen.intMat_open_compact | (intros; apply GlobalTheory.IntMatOpen.intMat_open_compact <;> assumption)
