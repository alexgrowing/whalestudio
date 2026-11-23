import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStatementHolds
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariants_statement_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.H0InvariantsTheorem D HW F := by
  first | exact @GlobalTheory.invariants_of_field_of_norms | exact GlobalTheory.invariants_of_field_of_norms | (intros; apply GlobalTheory.invariants_of_field_of_norms <;> assumption)
