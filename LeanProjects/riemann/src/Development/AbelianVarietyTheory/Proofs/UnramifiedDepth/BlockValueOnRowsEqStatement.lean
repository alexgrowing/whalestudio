import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockValueOnRowsEq
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockValue_on_rows_eq : BiValue := by
  first | exact @GlobalTheory.blockValue_rows | exact GlobalTheory.blockValue_rows | (intros; apply GlobalTheory.blockValue_rows <;> assumption)
