import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def FiniteMapOpen.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ),
    J.IsPrime → Function.Injective ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)) →
    ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).Finite →
    ∀ x ∈ zeroLocus J, ∀ U ∈ 𝓝 x,
      (fun z : Fin n → ℂ => fun i => eval z (p i)) '' (zeroLocus J ∩ U) ∈
        𝓝 (fun i => eval x (p i))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
