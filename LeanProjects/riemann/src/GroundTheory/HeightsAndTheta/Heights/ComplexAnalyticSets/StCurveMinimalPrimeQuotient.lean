import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def CurveMinimalPrimeQuotient.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (p : Ideal (curveLocalRing I q)),
    p ∈ minimalPrimes (curveLocalRing I q) →
      ∃ J : Ideal (MvPolynomial (Fin n) ℂ), J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧
        ∃ φ : curveLocalRing I q →+* curveLocalRing J q, Function.Surjective φ ∧ RingHom.ker φ = p ∧
          ∀ f : MvPolynomial (Fin n) ℂ, φ (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) =
            algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f

end

end GroundTheory.Heights₂.Heights
