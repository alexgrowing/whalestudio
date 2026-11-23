import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientData
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
open GlobalTheory.PsCo.Pc1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_pseudoCoefficientData : StKData := by
  first | exact @GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | exact GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | (intros; apply GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' <;> assumption)
