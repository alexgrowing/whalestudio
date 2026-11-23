import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffInDomainMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedCharpolyCoeffInDomain_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_mul | exact GlobalTheory.NormalDescent.normCoeff_mul | (intros; apply GlobalTheory.NormalDescent.normCoeff_mul <;> assumption)
