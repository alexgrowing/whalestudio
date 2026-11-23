import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWords
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) := by
  first | exact @GlobalTheory.EX.szRow_sizeG_sizeWords | exact GlobalTheory.EX.szRow_sizeG_sizeWords | (intros; apply GlobalTheory.EX.szRow_sizeG_sizeWords <;> assumption)
