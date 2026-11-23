import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLiftGlobalPrimitive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGraph
open GlobalTheory.PrimLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_lift_global_primitive : ∀ {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (P : Set X → (X → ℂ) → Prop),
    (∀ O f, P O f → IsOpen O) →
    (∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f) →
    (∀ O f (c : ℂ), P O f → P O (fun y => f y + c)) →
    (∀ x, ∃ O f, x ∈ O ∧ P O f) →
    IsCoveringMap (GlobalTheory.PrimLift.Etale.proj P) →
    ∃ F : X → ℂ, ∀ x, ∃ O f, x ∈ O ∧ P O f ∧ Set.EqOn F f O := by
  first | exact @GlobalTheory.exists_global_of_isCoveringMap_etale | exact GlobalTheory.exists_global_of_isCoveringMap_etale | (intros; apply GlobalTheory.exists_global_of_isCoveringMap_etale <;> assumption)
