import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

def CircleArgumentPrinciple.Statement : Prop :=
  ∀ (h : ℂ → ℂ) (O : Set ℂ) (c : ℂ) (r : ℝ),
    0 < r → IsOpen O → closedBall c r ⊆ O → DifferentiableOn ℂ h O → (∀ s ∈ sphere c r, h s ≠ 0) →
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) ∧
      ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ O →
        (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv h s / h s) = (Z.map φ).sum

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
