import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOLower
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_PP_pow_mul_dim_pow_div_le_TOv : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ^ 4 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ C.T.Cp / ((D.R.m : ℝ) * L.de2) ≤ ((TOv L.sc : ℕ) : ℝ)) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) * D.R.k / D.R.m ≤ ((TOv L.sc : ℕ) : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_TO_lower | exact GlobalTheory.EX.szRow_TO_lower | (intros; apply GlobalTheory.EX.szRow_TO_lower <;> assumption)
