import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def ContinuousRootHolomorphic.Statement : Prop :=
  ∀ (k : ℕ) (Q : MvPolynomial (Fin (k + 1)) ℂ) (O : Set (Fin k → ℂ)) (h : (Fin k → ℂ) → ℂ),
    IsOpen O → ContinuousOn h O → (∀ t ∈ O, eval (Fin.cons (h t) t : Fin (k + 1) → ℂ) Q = 0) →
    ∀ y ∈ O, eval (Fin.cons (h y) y : Fin (k + 1) → ℂ) (pderiv 0 Q) ≠ 0 → DifferentiableAt ℂ h y

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
