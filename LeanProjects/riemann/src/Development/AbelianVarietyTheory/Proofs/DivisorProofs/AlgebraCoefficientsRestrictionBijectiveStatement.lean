import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebra_coefficients_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 → ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.CxCoh.single_algebra_restriction_bijective | exact GlobalTheory.CxCoh.single_algebra_restriction_bijective | (intros; apply GlobalTheory.CxCoh.single_algebra_restriction_bijective <;> assumption)
