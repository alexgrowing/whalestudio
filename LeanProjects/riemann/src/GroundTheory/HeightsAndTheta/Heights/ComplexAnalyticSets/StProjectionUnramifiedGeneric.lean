import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianRankOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjectionUnramifiedGeneric.Statement : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (Q : Ideal (MvPolynomial (α ⊕ β) ℂ)) (r : ℕ)
    (q : Fin r → MvPolynomial (α ⊕ β) ℂ) (t : MvPolynomial (α ⊕ β) ℂ), Q.IsPrime →
    (∀ b : β, ∃ F : Polynomial (MvPolynomial α ℂ), F.Monic ∧
      F.eval₂ (rename Sum.inl : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial (α ⊕ β) ℂ).toRingHom (X (Sum.inr b)) ∈ Q) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial (α ⊕ β) ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        ∀ v : α ⊕ β → ℂ, (∀ a : α, v (Sum.inl a) = 0) →
          (∀ j, ∑ s, eval w (pderiv s (q j)) * v s = 0) → v = 0

end

end GroundTheory.Heights₂.Heights
