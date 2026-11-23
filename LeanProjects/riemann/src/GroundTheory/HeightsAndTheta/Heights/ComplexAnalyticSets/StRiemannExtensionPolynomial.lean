import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def RiemannExtensionPolynomial.Statement : Prop :=
  ∀ (k : ℕ) (P : MvPolynomial (Fin k) ℂ) (O : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → ℂ),
    P ≠ 0 → IsOpen O → ContinuousOn f O → DifferentiableOn ℂ f (O ∩ {y | eval y P ≠ 0}) →
    DifferentiableOn ℂ f O

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
