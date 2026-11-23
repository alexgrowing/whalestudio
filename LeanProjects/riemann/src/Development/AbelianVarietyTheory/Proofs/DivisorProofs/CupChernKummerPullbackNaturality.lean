import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6nat_holds : GlobalTheory.EtC.DivisorNaturality := by
  intro q _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f n m i j a b
    exact GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b
  · intro E E' f h
    exact (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.1 f h
  · intro E E' f L h
    exact (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 f L h
  · intro Y X f u h
    exact (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 f u h

end GlobalTheory.EtC
