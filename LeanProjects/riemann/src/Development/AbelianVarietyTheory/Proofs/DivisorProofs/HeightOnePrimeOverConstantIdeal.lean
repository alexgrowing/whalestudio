import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeUnique
import Mathlib
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_over_constant_ideal : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (p : Ideal A) [p.IsPrime], p.height = 1 →
    P.comap (algebraMap A[X] (Localization.AtPrime Q)) = p.map (Polynomial.C : A →+* A[X]) →
    (∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P)) ∧
      ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
  first | (exact @GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial) | (exact GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial) | (intros; apply GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial  <;> assumption)
