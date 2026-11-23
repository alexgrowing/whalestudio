import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowPpDimToLeRpow
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_PP_and_dim_and_TOv_le_x_rpow_Ct : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.x ^ L.Ct) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct) ∧ (((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct)) := by
  first | exact @GlobalTheory.EX.szRow_pp_dim_to_le_rpow | exact GlobalTheory.EX.szRow_pp_dim_to_le_rpow | (intros; apply GlobalTheory.EX.szRow_pp_dim_to_le_rpow <;> assumption)
