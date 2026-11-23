import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumDecayBound
import Mathlib
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_decay_bound : ∀ {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ), (∀ p, 0 < b p) → ∀ (h : S → ℝ≥0∞), Set.InjOn m {ξ | h ξ ≠ 0} → (∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) → ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  first | exact @GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | exact GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | (intros; apply GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn <;> assumption)
