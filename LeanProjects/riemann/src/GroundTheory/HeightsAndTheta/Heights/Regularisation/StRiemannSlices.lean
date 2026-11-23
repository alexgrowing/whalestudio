import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def RiemannExtensionSlices.Statement : Prop :=
  ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    DifferentiableOn ℂ G (ball (0 : Fin n → ℂ) 1 ∩ {z | ∀ i, z i ≠ 0}) →
    (∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c)) →
    ∃ G' : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ G' (ball (0 : Fin n → ℂ) 1) ∧
      ∀ z ∈ ball (0 : Fin n → ℂ) 1, (∀ i, z i ≠ 0) → G' z = G z

end

end GroundTheory.Heights₂.Heights.Regular
