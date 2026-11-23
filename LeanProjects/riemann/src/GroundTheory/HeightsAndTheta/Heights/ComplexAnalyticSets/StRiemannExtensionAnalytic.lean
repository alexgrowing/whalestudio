import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

noncomputable section

def RiemannExtensionAnalytic.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g f : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U →
    (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0) →
    DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}) →
    (∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0}))) →
    ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U ∩ {t | g t ≠ 0})

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
