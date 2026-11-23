import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactDvrAdicCompleteSeparatedUniformizer
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  first | exact @GlobalTheory.compact_dvr_complete_separated | exact GlobalTheory.compact_dvr_complete_separated | (intros; apply GlobalTheory.compact_dvr_complete_separated <;> assumption)
