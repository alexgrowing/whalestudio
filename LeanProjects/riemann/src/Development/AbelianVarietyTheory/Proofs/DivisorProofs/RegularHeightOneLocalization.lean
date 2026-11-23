import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualHopfOrderGaussSum
import Mathlib
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_height_one_localization : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
    (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime P) := by
  first | (exact @GlobalTheory.EtaleSpreadReg.isRegularLocalRing_atPrime) | (exact GlobalTheory.EtaleSpreadReg.isRegularLocalRing_atPrime) | (intros; apply GlobalTheory.EtaleSpreadReg.isRegularLocalRing_atPrime <;> assumption)
