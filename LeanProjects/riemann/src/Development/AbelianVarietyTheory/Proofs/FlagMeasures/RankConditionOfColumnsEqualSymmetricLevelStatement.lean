import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevel
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.HermitianForms.BothSym
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u := by
  first | exact @GlobalTheory.mu0Tie_of_colsTiedSym | exact GlobalTheory.mu0Tie_of_colsTiedSym | (intros; apply GlobalTheory.mu0Tie_of_colsTiedSym <;> assumption)
