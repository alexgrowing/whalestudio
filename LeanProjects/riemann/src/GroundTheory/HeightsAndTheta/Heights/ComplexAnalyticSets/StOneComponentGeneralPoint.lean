import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsBranchesGoodPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def OneComponentGeneralPoint.Statement : Prop :=
  ∀ (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)), W ∈ I.minimalPrimes →
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧
      GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ⊆
        closure (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ U) ∧
      ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ U, ∃ N ∈ 𝓝 x,
        GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ N ⊆ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
