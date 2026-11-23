import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerCosetRepresentativeTraceEqOfLtOne
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_cosetRepresentativeTrace_eq_of_lt_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (U : Subgroup G) [Fintype (G ⧸ U)], AlmostSep v U → ∀ e : L, (∀ g : G, g • e = e) → v e < 1 → ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e := by
  first | exact @GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | exact GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | (intros; apply GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' <;> assumption)
