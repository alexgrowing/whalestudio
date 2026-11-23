import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjSecDomain.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    W.IsPrime → ComplexSets.IsFiniteProjection W A →
      IsDomain (Vertical.SecAlg
          (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A)) ∧
        Module.Finite (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
          (Vertical.SecAlg
            (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
            (projPar A))

end

end GroundTheory.Heights₂.Heights
