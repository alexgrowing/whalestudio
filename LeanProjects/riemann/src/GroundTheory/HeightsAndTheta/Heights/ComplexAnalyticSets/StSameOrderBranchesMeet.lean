import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def SameOrderBranchesMeet.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c c' : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder c' f) →
      ∃ x ∈ c.image ∩ c'.image, x ≠ q

end

end GroundTheory.Heights₂.Heights
