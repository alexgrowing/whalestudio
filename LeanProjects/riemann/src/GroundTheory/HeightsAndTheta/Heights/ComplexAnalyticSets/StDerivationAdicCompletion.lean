import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def DerivationAdicCompletion.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Derivation ℤ R R),
    ∃ D' : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      ∀ r : R, D' (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) (D r)

noncomputable def polyDerivX : Derivation ℤ (MvPolynomial (Fin 1) ℂ) (MvPolynomial (Fin 1) ℂ) :=
  (MvPolynomial.pderiv (0 : Fin 1)).restrictScalars ℤ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
