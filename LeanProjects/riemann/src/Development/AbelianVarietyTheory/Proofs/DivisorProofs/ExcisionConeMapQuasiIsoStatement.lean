import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExcisionConeMapQuasiIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapCompAlgebraMap
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.excisionConeMap_quasiIso' : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  first | (exact @GlobalTheory.EtC.excisionConeMap_quasiIso) | (exact GlobalTheory.EtC.excisionConeMap_quasiIso) | (intros; apply GlobalTheory.EtC.excisionConeMap_quasiIso <;> assumption)
