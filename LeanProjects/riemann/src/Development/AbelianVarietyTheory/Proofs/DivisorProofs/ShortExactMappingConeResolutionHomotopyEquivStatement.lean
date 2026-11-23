import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact → ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃), Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  first | (exact @GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (exact GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (intros; apply GlobalTheory.EtC.cone_resMap_homotopyEquiv  <;> assumption)
