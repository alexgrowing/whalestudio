import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCover
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover : GlobalTheory.EtC.A5 := by
  first | exact @GlobalTheory.EtC.classes_die_on_etale_cover | exact GlobalTheory.EtC.classes_die_on_etale_cover | (intros; apply GlobalTheory.EtC.classes_die_on_etale_cover <;> assumption)
