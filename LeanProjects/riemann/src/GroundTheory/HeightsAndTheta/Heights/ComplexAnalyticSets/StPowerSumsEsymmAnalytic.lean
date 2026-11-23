import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def PowerSumsEsymmAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (V : Set (σ → ℂ)) (d : ℕ) (Z : (σ → ℂ) → Multiset ℂ),
    IsOpen V → (∀ z ∈ V, Multiset.card (Z z) = d) →
    (∀ k, 1 ≤ k → k ≤ d → AnalyticOnNhd ℂ (fun z => ((Z z).map fun a => a ^ k).sum) V) →
    ∀ k, AnalyticOnNhd ℂ (fun z => (Z z).esymm k) V

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
