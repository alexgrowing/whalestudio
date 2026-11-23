import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def RueckertNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (f i) w) → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, (∀ i, f i z = 0) → g z = 0) →
    ∃ (m : ℕ) (h : Fin k → (σ → ℂ) → ℂ), 0 < m ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
      ∀ᶠ z in 𝓝 w, g z ^ m = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
