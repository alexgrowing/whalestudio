import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_etale_vanishing : GlobalTheory.EtC.B6h1 := by
  first | (exact @GlobalTheory.EtC.kummer_vanishing) | (exact GlobalTheory.EtC.kummer_vanishing) | (intros; apply GlobalTheory.EtC.kummer_vanishing  <;> assumption)
