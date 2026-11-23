import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactScaledIntoNhds
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_scaled_into_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem | exact GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem | (intros; apply GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem <;> assumption)
