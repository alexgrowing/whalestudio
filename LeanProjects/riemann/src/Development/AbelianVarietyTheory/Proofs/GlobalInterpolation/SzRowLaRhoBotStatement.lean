import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLaRhoBot
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  first | exact @GlobalTheory.EX.szRow_la_rho_bot | exact GlobalTheory.EX.szRow_la_rho_bot | (intros; apply GlobalTheory.EX.szRow_la_rho_bot <;> assumption)
