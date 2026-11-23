import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLattice
import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameStabiliser_mapsTo_completedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  first | exact @GlobalTheory.stab_hatL_mapsTo | exact GlobalTheory.stab_hatL_mapsTo | (intros; apply GlobalTheory.stab_hatL_mapsTo <;> assumption)
