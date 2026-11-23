import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneCompleteIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def JacobianRankOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ)
    (t : MvPolynomial σ ℂ), Q.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (d : ℕ) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial σ ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j)))) + d =
          Fintype.card σ

end

end GroundTheory.Heights₂.Heights
