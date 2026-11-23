import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwist
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.red_c1_eq_c1_of_dvd : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1), red Q q E 2 1 (c1 Q L) = c1 q L := by
  first
  | exact @GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | exact GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | (intros; apply GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist <;> assumption)
