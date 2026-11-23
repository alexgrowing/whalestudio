import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProductWeightsLeOfSeparatedGeometricMean
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
open GlobalTheory.SepPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_productWeights_le_of_separated_geometricMean : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ la : ℝ, 0 < la → la ≤ 1 → ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ), (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) → ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) := by
  first | exact @GlobalTheory.SepSum.sum_weights_le_of_separated | exact GlobalTheory.SepSum.sum_weights_le_of_separated | (intros; apply GlobalTheory.SepSum.sum_weights_le_of_separated <;> assumption)
