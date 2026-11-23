import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def RemovableHyperplane.Statement : Prop :=
  ∀ (k n : ℕ) (R : ℝ) (f : (Fin (k + 1) → ℂ) → Fin n → ℂ),
    DifferentiableOn ℂ f (Metric.ball 0 R ∩ {t | t 0 ≠ 0}) →
    Bornology.IsBounded (f '' (Metric.ball 0 R ∩ {t | t 0 ≠ 0})) →
    ∃ g : (Fin (k + 1) → ℂ) → Fin n → ℂ, DifferentiableOn ℂ g (Metric.ball 0 R) ∧
      Set.EqOn g f (Metric.ball 0 R ∩ {t | t 0 ≠ 0})

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
