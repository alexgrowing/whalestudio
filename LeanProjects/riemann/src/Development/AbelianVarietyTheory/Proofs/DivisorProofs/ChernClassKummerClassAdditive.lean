import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6add_holds : GlobalTheory.EtC.DivisorAdditivity := by
  intro q _
  exact ⟨fun L M N hE hN => (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.2 L M N hE hN,
    fun u v hq => (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 u v hq⟩

end GlobalTheory.EtC
