import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Topology

noncomputable section

def FiniteProjectionCluster.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (w : Fin n → ℂ)
    (U : Set (Fin n → ℂ)),
    IsFiniteProjection J A → w ∈ zeroSet J → U ∈ 𝓝 w →
      ∃ (r : ℝ) (N M : Set (Fin n → ℂ)), 0 < r ∧ IsOpen N ∧ IsOpen M ∧ w ∈ N ∧ N ⊆ U ∧
        Disjoint N M ∧
        zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r} ⊆ N ∪ M ∧
        Bornology.IsBounded (zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r})

end

end GroundTheory.Heights₂.Heights.ComplexSets
