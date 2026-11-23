import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def SimpleRootBranch.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (τ : ℂ),
    (p.map (MvPolynomial.eval y)).IsRoot τ →
      (p.map (MvPolynomial.eval y)).derivative.eval τ ≠ 0 →
        ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
          IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ DifferentiableOn ℂ ψ U ∧ ψ y = τ ∧
            ∀ w ∈ U, ψ w ∈ B ∧
              ∀ s ∈ B, ((p.map (MvPolynomial.eval w)).IsRoot s ↔ s = ψ w)

end

end GroundTheory.Heights₂.Heights.ComplexSets
