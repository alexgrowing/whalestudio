import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCoveringMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGraph
open GlobalTheory.PrimLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_space_covering_map : ∀ {X : Type} [TopologicalSpace X] (P : Set X → (X → ℂ) → Prop),
    (∀ O f, P O f → IsOpen O) →
    (∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f) →
    (∀ O f (c : ℂ), P O f → P O (fun y => f y + c)) →
    (∀ x, ∃ O f, x ∈ O ∧ P O f) →
    (∀ O f g, P O f → P O g → IsOpen {y | y ∈ O ∧ f y = g y}) →
    IsCoveringMap (GlobalTheory.PrimLift.Etale.proj P) := by
  first | exact @GlobalTheory.PrimLift.Etale.isCoveringMap_proj | exact GlobalTheory.PrimLift.Etale.isCoveringMap_proj | (intros; apply GlobalTheory.PrimLift.Etale.isCoveringMap_proj <;> assumption)
