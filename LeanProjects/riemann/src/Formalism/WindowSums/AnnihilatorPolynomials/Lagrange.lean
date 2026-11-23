import Formalism.WindowSums.Statement

noncomputable section

namespace Formalism.WindowSums

open Polynomial

private lemma aeval_prod_X_sub_C_eq_zero_of_subset {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    (T : Module.End R V) {ι : Type} [DecidableEq ι] (A B : Finset ι) (γ : ι → R) (x : V)
    (hAB : A ⊆ B) (hA : aeval T (∏ k ∈ A, (X - C (γ k))) x = 0) :
    aeval T (∏ k ∈ B, (X - C (γ k))) x = 0 := by
  rw [← Finset.prod_sdiff hAB, map_mul, Module.End.mul_apply, hA, map_zero]

theorem lagrange_annihilation : Lagrange := by
  intro R _ _ V _ _ T ι _ I S γ d x hSI hinj hS hIS hdiv
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst hI
    have hS0 : S = ∅ := Finset.subset_empty.mp hSI
    subst hS0
    simp at hS
    simp [hS]
  choose! c hc using hdiv

  have key : ∑ k ∈ I, C (c k) * ∏ m ∈ I.erase k, (X - C (γ m)) = C d := by
    rw [← sub_eq_zero]
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (I.image γ)
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      rw [eval_sub, eval_finsetSum, eval_C, sub_eq_zero]
      rw [Finset.sum_eq_single j]
      · rw [eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        rw [hc j hj, mul_comm]
      · intro k hk hkj
        rw [eval_mul, eval_prod]
        apply mul_eq_zero_of_right
        apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨fun h => hkj h.symm, hj⟩)
        simp
      · intro hj'; exact absurd hj hj'
    · rw [Finset.card_image_of_injOn hinj]
      have hpos : 0 < I.card := Finset.card_pos.mpr hI
      have hdeg : ∀ k ∈ I, (C (c k) * ∏ m ∈ I.erase k, (X - C (γ m))).natDegree ≤ I.card - 1 := by
        intro k hk
        refine (natDegree_C_mul_le _ _).trans ?_
        refine (natDegree_prod_le _ _).trans ?_
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
        rw [Finset.card_erase_of_mem hk]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      rw [natDegree_C, max_lt_iff]
      refine ⟨lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ hdeg) (by omega), hpos⟩
  have h := congrArg (fun p => aeval T p x) key
  simp only [map_sum, aeval_C] at h
  rw [LinearMap.sum_apply] at h
  rw [Module.algebraMap_end_apply] at h
  rw [← h]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply]
  by_cases hkS : k ∈ S
  · have : I \ S ⊆ I.erase k := by
      intro m hm
      rw [Finset.mem_sdiff] at hm
      exact Finset.mem_erase.mpr ⟨fun h => hm.2 (h ▸ hkS), hm.1⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hIS, smul_zero]
  · have : S ⊆ I.erase k := by
      intro m hm
      exact Finset.mem_erase.mpr ⟨fun h => hkS (h ▸ hm), hSI hm⟩
    rw [aeval_prod_X_sub_C_eq_zero_of_subset T _ _ γ x this hS, smul_zero]

end Formalism.WindowSums
