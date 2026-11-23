import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneCompleteIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCodimOneUniformiser.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ) (x : MvPolynomial σ ℂ),
    P.IsPrime → Q.IsPrime → P ≤ Q → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
    x ∈ Q → x ∉ P →
      ∃ (g a b t : MvPolynomial σ ℂ) (k : ℕ), g ∈ Q ∧ 0 < k ∧ a ∉ Q ∧ b ∉ Q ∧ t ∉ Q ∧
        b * x - a * g ^ k ∈ P ∧ ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ P ⊔ Ideal.span {g}

end

end GroundTheory.Heights₂.Heights
