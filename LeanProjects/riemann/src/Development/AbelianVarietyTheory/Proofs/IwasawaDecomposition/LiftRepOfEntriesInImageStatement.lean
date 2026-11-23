import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftRepOfEntriesInImage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_lift_of_entries_mem_range : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  first | exact @GlobalTheory.lift_rep_of_entries_in_image | exact GlobalTheory.lift_rep_of_entries_in_image | (intros; apply GlobalTheory.lift_rep_of_entries_in_image <;> assumption)
