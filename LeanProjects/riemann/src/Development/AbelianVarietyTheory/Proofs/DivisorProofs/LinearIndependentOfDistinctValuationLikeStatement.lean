import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfDistinctValuationLike
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_injective_valuationLike : ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) → LinearIndependent C f := by
  first | exact @GlobalTheory.linearIndependent_of_distinct_valuationLike | exact GlobalTheory.linearIndependent_of_distinct_valuationLike | (intros; apply GlobalTheory.linearIndependent_of_distinct_valuationLike <;> assumption)
