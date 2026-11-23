import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_hypercohomology_bijective' : A1 := by
  intro R _ K L f _ F n
  haveI : (res R F).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).1
  exact GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R f (res R F) n

end GlobalTheory.EtC
