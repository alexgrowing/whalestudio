import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentSurjectsClopen
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_surjects_clopen : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  first | exact @GlobalTheory.clopen_image_irreducibleComponent | exact GlobalTheory.clopen_image_irreducibleComponent | (intros; apply GlobalTheory.clopen_image_irreducibleComponent <;> assumption)
