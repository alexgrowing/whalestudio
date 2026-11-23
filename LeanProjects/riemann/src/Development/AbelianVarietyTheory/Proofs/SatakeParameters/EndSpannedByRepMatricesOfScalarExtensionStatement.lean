import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedByRepMatricesOfScalarExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ} (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L)), EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L)))) → EndSpanned τ U := by
  first | exact @GlobalTheory.SplitField.endSpanned_of_endSpanned_map | exact GlobalTheory.SplitField.endSpanned_of_endSpanned_map | (intros; apply GlobalTheory.SplitField.endSpanned_of_endSpanned_map <;> assumption)
