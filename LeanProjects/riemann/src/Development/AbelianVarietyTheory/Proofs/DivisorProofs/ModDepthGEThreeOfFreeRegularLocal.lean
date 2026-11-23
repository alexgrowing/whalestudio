import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
open IsLocalRing RingTheory.Sequence

namespace GlobalTheory

theorem modDepthGE_three_of_free_of_isRegularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  intro R _ _ hd M _ _ _ _ _
  obtain ⟨xs, h, hl⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg : IsRegular R xs := isRegular_of_ofList_eq_maximalIdeal h hl.le
  have h3 : 3 ≤ xs.length := by
    rw [← hl] at hd
    exact_mod_cast hd
  have hm : ∀ r ∈ xs.take 3, r ∈ maximalIdeal R := fun r hr =>
    h ▸ Ideal.subset_span (List.mem_of_mem_take hr)
  have hw : IsWeaklyRegular R (xs.take 3) := by
    have := hreg.1
    rw [← List.take_append_drop 3 xs, isWeaklyRegular_append_iff] at this
    exact this.1
  have hwM : IsWeaklyRegular M (xs.take 3) := by
    have := hw.isWeaklyRegular_lTensor (M₂ := M)
    exact ((TensorProduct.rid R M).isWeaklyRegular_congr _).mp this
  refine ⟨xs.take 3, by simp [h3], hm, ?_⟩
  exact (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hwM

end GlobalTheory
