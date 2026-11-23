import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field : GlobalTheory.RegSS.CyclicField → GlobalTheory.RegSS.CyclicSemilocal := by
  first | exact @GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | exact GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | (intros; apply GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField <;> assumption)
