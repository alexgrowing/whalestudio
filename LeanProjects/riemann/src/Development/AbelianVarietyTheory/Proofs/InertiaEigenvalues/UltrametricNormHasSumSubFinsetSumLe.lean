import Mathlib
open Polynomial

namespace GlobalTheory

theorem norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  intro K _ _ ι f s I ε hε hs hf
  classical
  have h0 : Filter.Tendsto (fun J : Finset ι => ∑ i ∈ J, f i) Filter.atTop (nhds s) := hs
  have ht : Filter.Tendsto (fun J : Finset ι => ‖∑ i ∈ J, f i - ∑ i ∈ I, f i‖) Filter.atTop
      (nhds ‖s - ∑ i ∈ I, f i‖) :=
    (h0.sub tendsto_const_nhds).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop I] with J hJ
  rw [← Finset.sum_sdiff hJ, add_sub_cancel_right]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun i hi =>
    hf i (Finset.mem_sdiff.mp hi).2

end GlobalTheory
