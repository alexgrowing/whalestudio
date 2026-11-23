import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStar
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar : SzRow (fun C D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧ (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  first | exact @GlobalTheory.EX.szRow_lStar | exact GlobalTheory.EX.szRow_lStar | (intros; apply GlobalTheory.EX.szRow_lStar <;> assumption)
