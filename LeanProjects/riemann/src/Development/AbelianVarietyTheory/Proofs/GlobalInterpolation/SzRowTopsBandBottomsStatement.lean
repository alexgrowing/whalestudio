import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTopsBandBottoms
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_card_TT_le_Nstar_and_rhoP_le_and_bT_le : SzRow (fun C D L => ((D.host.TT.card : ℝ) ≤ Nstar L) ∧ (rhoP L C.P.Crho ≤ L.sc.x ^ (-2 : ℝ)) ∧ (∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k)) := by
  first | exact @GlobalTheory.EX.szRow_tops_band_bottoms | exact GlobalTheory.EX.szRow_tops_band_bottoms | (intros; apply GlobalTheory.EX.szRow_tops_band_bottoms <;> assumption)
