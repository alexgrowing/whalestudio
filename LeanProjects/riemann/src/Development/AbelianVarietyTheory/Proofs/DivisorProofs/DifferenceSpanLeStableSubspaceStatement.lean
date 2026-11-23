import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceSpanLeStableSubspace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.difference_span_le_stable_subspace : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → (∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W) → ∀ (y : k) (r : kˣ) (c : ℂ), c ≠ 0 → ValuativeRel.valuation k (r : k) < ValuativeRel.valuation k y → c • GlobalTheory.PrinTwo.elemDiff 0 y r ∈ W → GlobalTheory.PrinTwo.elemSpan k ≤ W := by
  first | exact @GlobalTheory.PrinTwo.DiffSpan.elemSpan_le | exact GlobalTheory.PrinTwo.DiffSpan.elemSpan_le | (intros; apply GlobalTheory.PrinTwo.DiffSpan.elemSpan_le <;> assumption)
