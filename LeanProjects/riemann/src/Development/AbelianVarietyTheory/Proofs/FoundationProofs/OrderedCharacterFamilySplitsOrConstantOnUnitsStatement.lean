import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnits
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  first | exact @GlobalTheory.PsType.cut_or_const | exact GlobalTheory.PsType.cut_or_const | (intros; apply GlobalTheory.PsType.cut_or_const <;> assumption)
