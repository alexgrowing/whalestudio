import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPseudoCoefficientExistenceUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
open GlobalTheory.PsCo.Pc1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPseudoCoefficientExistence_unitaryGroup : GlobalTheory.PsCo.Pc.LocalPC := by
  first | exact @GlobalTheory.PsCo.Pc.localPC_holds | exact GlobalTheory.PsCo.Pc.localPC_holds | (intros; apply GlobalTheory.PsCo.Pc.localPC_holds <;> assumption)
