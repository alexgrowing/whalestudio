import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeLstar
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := by
  first | exact @GlobalTheory.EX.szRow_sizeLstar | exact GlobalTheory.EX.szRow_sizeLstar | (intros; apply GlobalTheory.EX.szRow_sizeLstar <;> assumption)
