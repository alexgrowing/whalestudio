import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine : Big fun ch => PeriodsOnLine ch := by
  first | exact @GlobalTheory.RowReal.periodsOnLine_big | exact GlobalTheory.RowReal.periodsOnLine_big | (intros; apply GlobalTheory.RowReal.periodsOnLine_big <;> assumption)
