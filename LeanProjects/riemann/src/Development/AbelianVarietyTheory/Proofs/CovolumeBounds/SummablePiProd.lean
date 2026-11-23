import Mathlib

namespace GlobalTheory.SummablePiProd

universe u_1 u_2

theorem summable_pi_prod {ι : Type u_1} [inst : Fintype ι] {J : ι → Type u_2}
    {u : (i : ι) → J i → ℝ} (h0 : ∀ (i : ι) (j : J i), (0 : ℝ) ≤ u i j)
    (hs : ∀ (i : ι), Summable (u i)) :
    Summable fun (t : (i : ι) → J i) ↦ ∏ i : ι, u i (t i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' j, u i j)
    (fun t => Finset.prod_nonneg fun i _ => h0 i (t i)) ?_
  intro s
  calc ∑ t ∈ s, ∏ i, u i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, u i (t i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun t _ _ => Finset.prod_nonneg fun i _ => h0 i (t i))
        intro t ht
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ j ∈ s.image (fun t => t i), u i j := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' j, u i j := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => h0 i j) ?_
        intro i _
        exact (hs i).sum_le_tsum _ (fun j _ => h0 i j)

end GlobalTheory.SummablePiProd
