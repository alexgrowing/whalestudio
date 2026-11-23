import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolomorphicKernelFibre.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (b : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → b ∈ U →
    ∀ d : ℕ, Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) = d →
      ∃ (V : Set (Fin d → ℂ)) (y : Fin d → ℂ) (γ : (Fin d → ℂ) → Fin k → ℂ)
        (ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ),
        IsOpen V ∧ y ∈ V ∧ DifferentiableOn ℂ γ V ∧ Set.MapsTo γ V U ∧ Set.InjOn γ V ∧
          (∀ s ∈ V, ∀ t ∈ V, ℓ (f (γ s)) = ℓ (f (γ t)) → f (γ s) = f (γ t)) ∧
          fderiv ℂ (fun t => ℓ (f (γ t))) y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
