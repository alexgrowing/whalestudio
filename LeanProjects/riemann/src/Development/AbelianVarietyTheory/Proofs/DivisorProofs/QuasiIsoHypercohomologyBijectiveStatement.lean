import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_hypercohomology_bijective : GlobalTheory.EtC.A1 := by
  first | (exact @GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (exact GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (intros; apply GlobalTheory.EtC.quasiIso_hypercohomology_bijective'  <;> assumption)
