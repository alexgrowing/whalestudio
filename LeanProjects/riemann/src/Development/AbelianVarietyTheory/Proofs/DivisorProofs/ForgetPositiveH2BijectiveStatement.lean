import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH2Bijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forget_positive_h2_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac1 → K.M1.Ac2 → K.M2.Ac0 → K.M2.Ac1 → K.M3.Ac0 → Function.Bijective K.fnMap.h2 := by
  first | exact @GlobalTheory.CxCoh.fnMap_h2_bijective | exact GlobalTheory.CxCoh.fnMap_h2_bijective | (intros; apply GlobalTheory.CxCoh.fnMap_h2_bijective <;> assumption)
