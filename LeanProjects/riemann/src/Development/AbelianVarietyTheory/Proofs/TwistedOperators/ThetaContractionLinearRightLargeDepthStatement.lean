import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearRightLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaContraction_linear_right_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 1 := by
  first | exact @GlobalTheory.ConLinR.contrLin_one_big | exact GlobalTheory.ConLinR.contrLin_one_big | (intros; apply GlobalTheory.ConLinR.contrLin_one_big <;> assumption)
