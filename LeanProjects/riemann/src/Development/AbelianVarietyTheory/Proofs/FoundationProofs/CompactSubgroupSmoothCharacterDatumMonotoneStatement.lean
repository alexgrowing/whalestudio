import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSubgroupSmoothCharacterDatumMonotone
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSubgroupSmoothCharacterDatum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  first | exact @GlobalTheory.StripGrp.strip_datum_monotone | exact GlobalTheory.StripGrp.strip_datum_monotone | (intros; apply GlobalTheory.StripGrp.strip_datum_monotone <;> assumption)
