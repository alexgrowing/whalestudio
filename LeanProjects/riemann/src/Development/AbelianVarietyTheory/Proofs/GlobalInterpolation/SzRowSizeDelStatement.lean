import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeDel
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeDel : SzRow (fun _ _ L => SizeDel L) := by
  first | exact @GlobalTheory.EX.szRow_sizeDel | exact GlobalTheory.EX.szRow_sizeDel | (intros; apply GlobalTheory.EX.szRow_sizeDel <;> assumption)
