import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

noncomputable section

def PowerUnitCount.Statement : Prop :=
  ∀ (d m : ℕ) (O : Set (Fin (d + 1) → ℂ)) (F : (Fin (d + 1) → ℂ) → Fin d → ℂ)
    (H : (Fin (d + 1) → ℂ) → ℂ) (s : Fin (d + 1) → ℂ),
    IsOpen O → s ∈ O → s 0 = 0 → DifferentiableOn ℂ F O → DifferentiableOn ℂ H O → H s ≠ 0 →
    Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0) (F τ)) s) →
    ∃ P₀ ∈ 𝓝 s, Set.InjOn F (P₀ ∩ {τ | τ 0 = 0}) ∧
      ∀ P ∈ 𝓝 s, P ⊆ P₀ → ∃ (V : Set (Fin d → ℂ)) (ρ : ℝ), IsOpen V ∧ F s ∈ V ∧ 0 < ρ ∧
        (∀ w ∈ V, ∀ τ ∈ P₀, τ 0 = 0 → F τ = w → τ ∈ P) ∧
        ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
          {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t}.encard = m

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
