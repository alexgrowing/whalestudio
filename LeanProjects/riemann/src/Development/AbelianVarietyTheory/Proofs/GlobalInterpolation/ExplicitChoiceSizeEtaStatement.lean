import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeEta
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  first | exact @GlobalTheory.EX.szRow_sizeEta | exact GlobalTheory.EX.szRow_sizeEta | (intros; apply GlobalTheory.EX.szRow_sizeEta <;> assumption)
