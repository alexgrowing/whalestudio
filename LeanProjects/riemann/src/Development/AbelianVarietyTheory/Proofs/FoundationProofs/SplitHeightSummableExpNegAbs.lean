import Mathlib

namespace GlobalTheory

open Finset

open Finset in

theorem _root_.GlobalTheory.splitHeight_summable_pi_prod {ι : Type} [Fintype ι] {α : ι → Type} {f : ∀ i, α i → ℝ}
    (h0 : ∀ i x, 0 ≤ f i x) (hf : ∀ i, Summable (f i)) :
    Summable fun n : ∀ i, α i => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i (n i)) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image fun n : (∀ i, α i) => n i, ∏ i, f i (n i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
          Finset.prod_nonneg fun i _ => h0 i (n i)
        intro n hn
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hn
    _ = ∏ i, ∑ x ∈ s.image fun n : (∀ i, α i) => n i, f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' x, f i x := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

end GlobalTheory
