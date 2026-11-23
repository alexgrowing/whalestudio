import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologyTwoSubsingleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingletonStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.etC_c2 : GlobalTheory.EtC.C2 := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed q k B hq i
  · exact GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three q k B hq n i (by omega)

end GlobalTheory
