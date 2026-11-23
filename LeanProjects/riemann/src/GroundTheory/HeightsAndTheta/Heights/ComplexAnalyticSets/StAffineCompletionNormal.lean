import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AffineCompletionNormal.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (m : Ideal (MvPolynomial σ ℂ ⧸ I)),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → m.IsMaximal →
      IsDomain (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) ∧
        IsIntegrallyClosed (AdicCompletion m (MvPolynomial σ ℂ ⧸ I))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
