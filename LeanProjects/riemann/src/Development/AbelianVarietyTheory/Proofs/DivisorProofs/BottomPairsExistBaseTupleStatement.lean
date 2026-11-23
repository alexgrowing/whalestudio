import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistBaseTuple
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomPairs_exist_baseTuple : (∀ D, GlobalTheory.NormSum.Inp D) → BotEx := by
  first | exact @GlobalTheory.SqTop.botEx_holds | exact GlobalTheory.SqTop.botEx_holds | (intros; apply GlobalTheory.SqTop.botEx_holds <;> assumption)
