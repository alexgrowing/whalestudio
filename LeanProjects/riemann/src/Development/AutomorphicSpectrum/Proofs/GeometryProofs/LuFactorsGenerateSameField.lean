import Mathlib

namespace GlobalTheory.CompanionTheory.LuFields

open Matrix

theorem entries_mem_of_eq_mul {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (F : IntermediateField K L) (C v w : Matrix (Fin n) (Fin n) L) (hC : ∀ i k, C i k ∈ F)
    (hv1 : ∀ k, v k k = 1) (hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0) (h : C = v * w) :
    (∀ i k, v i k ∈ F) ∧ (∀ i k, w i k ∈ F) := by
  have hC' : ∀ i k, ∑ l, v i l * w l k ∈ F := fun i k => by
    have := hC i k
    rwa [h, Matrix.mul_apply] at this
  have key : ∀ m : ℕ, ∀ i k : Fin n, ((i : ℕ) < m ∨ (k : ℕ) < m) → v i k ∈ F ∧ w i k ∈ F := by
    intro m
    induction m with
    | zero => intro i k hik; exact absurd hik (by omega)
    | succ m ih =>
      have hw : ∀ i k : Fin n, (i : ℕ) = m → i ≤ k → w i k ∈ F := by
        intro i k hi hik
        have hsum := hC' i k
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hv1, one_mul] at hsum
        have hrest : ∑ l ∈ Finset.univ.erase i, v i l * w l k ∈ F := by
          refine sum_mem fun l hl => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlt | hgt
          · have hl' : (l : ℕ) < m := by have := Fin.lt_def.1 hlt; omega
            exact F.mul_mem (ih i l (Or.inr hl')).1 (ih l k (Or.inl hl')).2
          · rw [hv0 i l hgt, zero_mul]
            exact F.zero_mem
        simpa using F.sub_mem hsum hrest
      have hv : ∀ i k : Fin n, (k : ℕ) = m → k < i → v i k ∈ F := by
        intro i k hk hki
        have hwk : w k k ∈ F := hw k k hk le_rfl
        have hsum := hC' i k
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
        have hrest : ∑ l ∈ Finset.univ.erase k, v i l * w l k ∈ F := by
          refine sum_mem fun l hl => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlt | hgt
          · have hl' : (l : ℕ) < m := by have := Fin.lt_def.1 hlt; omega
            exact F.mul_mem (ih i l (Or.inr hl')).1 (ih l k (Or.inl hl')).2
          · rw [hw0 l k hgt, mul_zero]
            exact F.zero_mem
        have h1 : v i k * w k k ∈ F := by simpa using F.sub_mem hsum hrest
        have h2 := F.mul_mem h1 (F.inv_mem hwk)
        rwa [mul_assoc, mul_inv_cancel₀ (hwd k), mul_one] at h2
      intro i k hik
      by_cases h' : (i : ℕ) < m ∨ (k : ℕ) < m
      · exact ih i k h'
      · push_neg at h'
        rcases le_or_gt i k with hle | hlt
        · have hi : (i : ℕ) = m := by have := Fin.le_def.1 hle; omega
          refine ⟨?_, hw i k hi hle⟩
          rcases eq_or_lt_of_le hle with heq | hlt'
          · rw [heq, hv1]
            exact F.one_mem
          · rw [hv0 i k hlt']
            exact F.zero_mem
        · have hk : (k : ℕ) = m := by have := Fin.lt_def.1 hlt; omega
          refine ⟨hv i k hk hlt, ?_⟩
          rw [hw0 i k hlt]
          exact F.zero_mem
  exact ⟨fun i k => (key (i + 1) i k (Or.inl (Nat.lt_succ_self _))).1,
    fun i k => (key (i + 1) i k (Or.inl (Nat.lt_succ_self _))).2⟩

theorem adjoin_entries_eq (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L) (hA : A.det ≠ 0)
    (hu1 : ∀ k, u k k = 1) (hu0 : ∀ l k, l < k → u l k = 0)
    (hv1 : ∀ k, v k k = 1) (hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0)
    (h : A.map (algebraMap K L) * u = v * w) :
    IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) =
      IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  have hwT : w.BlockTriangular id := by
    intro l k hkl
    exact hw0 l k hkl
  have hdetw : w.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hwT]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hwd k
  have := Matrix.invertibleOfIsUnitDet w (isUnit_iff_ne_zero.2 hdetw)
  have hwiT : w⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hwT
  have hwwi : w * w⁻¹ = 1 := Matrix.mul_nonsing_inv w (isUnit_iff_ne_zero.2 hdetw)
  have hwid : ∀ k, w⁻¹ k k ≠ 0 := by
    intro k hk
    have e := congrFun (congrFun hwwi k) k
    rw [Matrix.mul_apply, Finset.sum_eq_single k, hk, mul_zero, Matrix.one_apply_eq] at e
    · exact zero_ne_one e
    · intro l _ hlk
      rcases lt_or_gt_of_ne hlk with hlt | hgt
      · rw [hw0 k l hlt, zero_mul]
      · rw [hwiT hgt, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hA)
  have hBAm : A⁻¹.map (algebraMap K L) * A.map (algebraMap K L) = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hC' : A⁻¹.map (algebraMap K L) * v = u * w⁻¹ := by
    have hu : u = A⁻¹.map (algebraMap K L) * v * w := by
      rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hBAm, Matrix.one_mul]
    rw [hu, Matrix.mul_assoc, hwwi, Matrix.mul_one]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    have hC : ∀ i k, (A⁻¹.map (algebraMap K L) * v) i k ∈
        IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
      intro i k
      rw [Matrix.mul_apply]
      refine sum_mem fun l _ => IntermediateField.mul_mem _ ?_ ?_
      · rw [Matrix.map_apply]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin K _ ⟨(l, k), rfl⟩
    exact (entries_mem_of_eq_mul _ _ u w⁻¹ hC hu1 hu0 (fun l k hkl => hwiT hkl) hwid hC').1 p.1 p.2
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    have hC : ∀ i k, (A.map (algebraMap K L) * u) i k ∈
        IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) := by
      intro i k
      rw [Matrix.mul_apply]
      refine sum_mem fun l _ => IntermediateField.mul_mem _ ?_ ?_
      · rw [Matrix.map_apply]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin K _ ⟨(l, k), rfl⟩
    exact (entries_mem_of_eq_mul _ _ v w hC hv1 hv0 hw0 hwd h).1 p.1 p.2

end GlobalTheory.CompanionTheory.LuFields
