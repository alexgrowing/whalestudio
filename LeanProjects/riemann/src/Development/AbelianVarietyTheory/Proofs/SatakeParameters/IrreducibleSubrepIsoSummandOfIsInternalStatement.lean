import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubrepIsoSummandOfIsInternal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)), DirectSum.IsInternal Us → (∀ m, IsIrrSub τ (Us m)) → ∀ W, IsIrrSub τ W → ∃ m, IsoSub τ W (Us m) := by
  first | exact @GlobalTheory.SplitField.isoSub_summand_of_isInternal | exact GlobalTheory.SplitField.isoSub_summand_of_isInternal | (intros; apply GlobalTheory.SplitField.isoSub_summand_of_isInternal <;> assumption)
