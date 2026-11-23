import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def VanishNearPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    J.IsPrime → x ∈ zeroLocus J → (∀ᶠ y in 𝓝 x, y ∈ zeroLocus J → eval y f = 0) → f ∈ J

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
