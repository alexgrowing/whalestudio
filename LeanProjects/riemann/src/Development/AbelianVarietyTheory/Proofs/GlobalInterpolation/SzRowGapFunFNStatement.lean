import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowGapFunFN
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_t_add_cube_le_h0_and_f_mul_N_pow_le_h0 : SzRow (fun C D L => ((D.R.t : ℝ) + 2 * ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 + 1 ≤ h0 L) ∧ ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ h0 L)) := by
  first | exact @GlobalTheory.EX.szRow_gap_fun_fN | exact GlobalTheory.EX.szRow_gap_fun_fN | (intros; apply GlobalTheory.EX.szRow_gap_fun_fN <;> assumption)
