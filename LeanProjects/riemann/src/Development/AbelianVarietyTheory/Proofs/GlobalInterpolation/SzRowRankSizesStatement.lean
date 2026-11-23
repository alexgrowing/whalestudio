import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankSizes
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeN_sizeM_sizeK_sizeT_sizeTT_sizeDe2_sizeLw : SzRow (fun _ _ L => SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeT L ∧ SizeTT L ∧ SizeDe2 L ∧ SizeLw L) := by
  first | exact @GlobalTheory.EX.szRow_rankSizes | exact GlobalTheory.EX.szRow_rankSizes | (intros; apply GlobalTheory.EX.szRow_rankSizes <;> assumption)
