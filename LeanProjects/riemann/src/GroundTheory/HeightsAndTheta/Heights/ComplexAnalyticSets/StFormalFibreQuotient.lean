import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibreQuotient.Statement : Prop :=
  ∀ (B A : Type) [CommRing B] [CommRing A] (f : B →+* A), Function.Surjective f → IsNoetherianRing B →
    ∀ (m : Ideal A) (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      ∃ P' : PrimeSpectrum (AdicCompletion (m.comap f) B),
        P'.asIdeal.comap (algebraMap B (AdicCompletion (m.comap f) B)) =
            (P.comap (algebraMap A (AdicCompletion m A))).comap f ∧
          Nonempty (primeFibreLocalRing A P ≃+* primeFibreLocalRing B P'.asIdeal)

noncomputable def dropSecondVariable : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval fun i => if i = 0 then MvPolynomial.X 0 else 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
