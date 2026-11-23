import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLe
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  first | exact @GlobalTheory.norm_hasSum_sub_finset_sum_le | exact GlobalTheory.norm_hasSum_sub_finset_sum_le | (intros; apply GlobalTheory.norm_hasSum_sub_finset_sum_le <;> assumption)
