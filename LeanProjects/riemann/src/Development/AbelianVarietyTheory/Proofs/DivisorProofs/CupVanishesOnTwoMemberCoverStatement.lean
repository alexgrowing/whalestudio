import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCover
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_vanishes_on_two_member_cover : GlobalTheory.EtC.DivisorSupportCondition := by
  first | (exact @GlobalTheory.EtC.a6supp) | (exact GlobalTheory.EtC.a6supp) | (intros; apply GlobalTheory.EtC.a6supp  <;> assumption)
