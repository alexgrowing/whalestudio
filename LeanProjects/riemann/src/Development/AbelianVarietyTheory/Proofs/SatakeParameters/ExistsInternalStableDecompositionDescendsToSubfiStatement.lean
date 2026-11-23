import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfi
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)), DirectSum.IsInternal Vs → (∀ m, IsInv (mapRep f τ) (Vs m)) → (∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) → ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧ ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  first | exact @GlobalTheory.SplitField.descend_decomp | exact GlobalTheory.SplitField.descend_decomp | (intros; apply GlobalTheory.SplitField.descend_decomp <;> assumption)
