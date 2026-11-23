import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_bijective_of_support_bijective : GlobalTheory.EtC.A10 := by
  first | (exact @GlobalTheory.EtC.a10) | (exact GlobalTheory.EtC.a10) | (intros; apply GlobalTheory.EtC.a10  <;> assumption)
