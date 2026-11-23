import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceRowWeightRatioAndLastCloudLeTwiceF
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_rowWeight_ratio_and_lastCloud_le_twice_first : SzRow (fun C D L => (∀ j j' τ τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m → wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ') ∧ (∀ τ (hm : 0 < D.R.m), (D.hc τ).b ⟨D.R.m - 1, by omega⟩ ≤ 2 * (D.hc τ).b ⟨0, hm⟩)) := by
  first | exact @GlobalTheory.EX.szRow_size_ratio | exact GlobalTheory.EX.szRow_size_ratio | (intros; apply GlobalTheory.EX.szRow_size_ratio <;> assumption)
