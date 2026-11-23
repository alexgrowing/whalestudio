import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceWindowRankLePolyBound
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_windowRank_le_polyBound : SzRow (fun C D L => ((2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP)) ∧ (((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP))) := by
  first | exact @GlobalTheory.EX.szRow_nW_le_PP | exact GlobalTheory.EX.szRow_nW_le_PP | (intros; apply GlobalTheory.EX.szRow_nW_le_PP <;> assumption)
