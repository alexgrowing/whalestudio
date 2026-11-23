import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveLieLatticeDegree
import Mathlib
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_contraction_of_etale_prime : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (a : A), a ≠ 0 → algebraMap A (Localization.AtPrime Q) a ∈ P → P.height ≤ 1 →
    (P.comap (algebraMap A (Localization.AtPrime Q))).height = 1 ∧
      P.comap (algebraMap A[X] (Localization.AtPrime Q)) =
        (P.comap (algebraMap A (Localization.AtPrime Q))).map (Polynomial.C : A →+* A[X]) := by
  first | (exact @GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C) | (exact GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C) | (intros; apply GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C  <;> assumption)
