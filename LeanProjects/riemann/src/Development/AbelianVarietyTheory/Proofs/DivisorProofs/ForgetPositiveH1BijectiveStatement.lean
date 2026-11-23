import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH1Bijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forget_positive_h1_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac0 → K.M1.Ac1 → K.M2.Ac0 → Function.Bijective K.fnMap.h1 := by
  first | exact @GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | exact GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | (intros; apply GlobalTheory.CxCoh.Cx.fnMap_h1_bijective <;> assumption)
