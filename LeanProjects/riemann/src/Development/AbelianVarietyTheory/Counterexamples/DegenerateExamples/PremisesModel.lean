import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum

open Finset Matrix

namespace GlobalTheory.IwahoriNewtonTest

open Finset Matrix in
private theorem isUnit_add_mul_of_mem_maximalIdeal {O : Type*} [CommRing O] [IsLocalRing O] {ϖ : O}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) {u : O} (hu : IsUnit u) (c : O) :
    IsUnit (u + ϖ * c) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add,
    (IsLocalRing.residue_eq_zero_iff _).mpr (Ideal.mul_mem_right c _ hϖ), add_zero,
    IsLocalRing.residue_ne_zero_iff_isUnit]
  exact hu

open Finset Matrix in
private theorem isUnit_diag_dvd_lower_mul {O : Type*} [CommRing O] [IsLocalRing O] {ϖ : O}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) {r : ℕ} (A B : Matrix (Fin r) (Fin r) O)
    (hA : ∀ i, IsUnit (A i i)) (hB : ∀ i, IsUnit (B i i))
    (hA' : ∀ i j, j < i → ϖ ∣ A i j) (hB' : ∀ i j, j < i → ϖ ∣ B i j) :
    (∀ i, IsUnit ((A * B) i i)) ∧ ∀ i j, j < i → ϖ ∣ (A * B) i j := by
  constructor
  · intro i
    rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hs : ϖ ∣ ∑ l ∈ univ.erase i, A i l * B l i := by
      refine Finset.dvd_sum fun l hl => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with h | h
      · exact Dvd.dvd.mul_right (hA' i l h) _
      · exact Dvd.dvd.mul_left (hB' l i h) _
    obtain ⟨c, hc⟩ := hs
    rw [hc]
    exact isUnit_add_mul_of_mem_maximalIdeal hϖ ((hA i).mul (hB i)) c
  · intro i j hij
    rw [mul_apply]
    refine Finset.dvd_sum fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · exact Dvd.dvd.mul_right (hA' i l h) _
    · exact Dvd.dvd.mul_left (hB' l j (lt_of_lt_of_le hij h)) _

open Finset Matrix in
private theorem isUnit_det_of_isUnit_diag_of_dvd_lower {O : Type*} [CommRing O] [IsLocalRing O] {ϖ : O}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (N : Matrix ι ι O) (hd : ∀ i, IsUnit (N i i)) (hl : ∀ i j, j < i → ϖ ∣ N i j) :
    IsUnit N.det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have htri : (N.map (IsLocalRing.residue O)).BlockTriangular id := by
    intro i j hij
    obtain ⟨c, hc⟩ := hl i j hij
    simp only [map_apply, hc]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (Ideal.mul_mem_right _ _ hϖ)
  rw [RingHom.mapMatrix_apply, Matrix.det_of_upperTriangular htri]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  simpa [IsLocalRing.residue_ne_zero_iff_isUnit] using hd i

open Finset Matrix in
private theorem card_filter_sub_le_eq (r k : ℕ) (hk : k ≤ r) :
    (univ.filter fun j : Fin r => r - k ≤ (j : ℕ)).card = k := by
  have : (univ.filter fun j : Fin r => r - k ≤ (j : ℕ)).map Fin.valEmbedding = Finset.Ico (r - k) r := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨hj, j.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← card_map, this, Nat.card_Ico]; omega

open Finset Matrix in
private theorem sum_filter_lt_sum_of_strictAnti {r : ℕ} {a : Fin r → ℕ} (ha : StrictAnti a) (k : ℕ)
    (s : Finset (Fin r)) (hs : s.card = (univ.filter fun j : Fin r => r - k ≤ (j : ℕ)).card)
    (hne : s ≠ univ.filter fun j : Fin r => r - k ≤ (j : ℕ)) :
    ∑ j ∈ univ.filter (fun j : Fin r => r - k ≤ (j : ℕ)), a j < ∑ j ∈ s, a j := by
  set T := univ.filter fun j : Fin r => r - k ≤ (j : ℕ)
  have hcard : (s \ T).card = (T \ s).card := by
    have h1 := card_sdiff_add_card_inter s T
    have h2 := card_sdiff_add_card_inter T s
    rw [inter_comm] at h2; omega
  have hne' : (s \ T).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
    intro hsub
    exact hne (eq_of_subset_of_card_le hsub hs.ge)
  obtain ⟨x, hx, hmin⟩ := (s \ T).exists_min_image a hne'
  have hlt : ∀ y ∈ T \ s, a y < a x := by
    intro y hy
    have hxT : ¬ (r - k ≤ (x : ℕ)) := by simpa [T] using (mem_sdiff.mp hx).2
    have hyT : r - k ≤ (y : ℕ) := by simpa [T] using (mem_sdiff.mp hy).1
    exact ha (show x < y from Fin.lt_def.mpr (by omega))
  have hT : ∑ j ∈ T \ s, a j < ∑ j ∈ s \ T, a j := by
    have hn : (T \ s).Nonempty := by rw [← card_pos, ← hcard]; exact card_pos.mpr hne'
    calc ∑ j ∈ T \ s, a j < ∑ _j ∈ T \ s, a x := sum_lt_sum_of_nonempty hn hlt
      _ = ∑ _j ∈ s \ T, a x := by simp [hcard]
      _ ≤ ∑ j ∈ s \ T, a j := sum_le_sum hmin
  have e1 := sum_sdiff (f := a) (inter_subset_left : s ∩ T ⊆ s)
  have e2 := sum_sdiff (f := a) (inter_subset_right : s ∩ T ⊆ T)
  rw [sdiff_inter_self_left] at e1
  rw [sdiff_inter_self_right] at e2
  omega

open Finset Matrix in

theorem _root_.GlobalTheory.IwahoriNewtonTest.intersectionNumber_baseChange : _root_.Formalism.PacketSums.IwahoriNewton := by
  unfold _root_.Formalism.PacketSums.IwahoriNewton
  intro O _ _ ϖ hϖ r a ha i₁ i₂ h1 h2 h1' h2' k hk
  have hc : ((i₁ * diagonal fun i => ϖ ^ a i) * i₂).charpoly
      = ((i₂ * i₁) * diagonal fun i => ϖ ^ a i).charpoly := by
    rw [charpoly_mul_comm, ← mul_assoc]
  obtain ⟨hU, hU'⟩ := isUnit_diag_dvd_lower_mul hϖ i₂ i₁ h2 h1 h2' h1'
  set U := i₂ * i₁
  have key := charpoly_coeff_eq_sum_minors (U * diagonal fun i => ϖ ^ a i) k (by simpa using hk)
  rw [Fintype.card_fin] at key
  rw [hc, key]
  have hminor : ∀ s : Finset (Fin r),
      ((U * diagonal fun i => ϖ ^ a i).submatrix (Subtype.val : s → Fin r) Subtype.val).det
        = ϖ ^ (∑ j ∈ s, a j) * (U.submatrix (Subtype.val : s → Fin r) Subtype.val).det := by
    intro s
    have : (U * diagonal fun i => ϖ ^ a i).submatrix (Subtype.val : s → Fin r) Subtype.val
        = U.submatrix Subtype.val Subtype.val * diagonal (fun j : s => ϖ ^ a j) := by
      ext i j; simp [mul_diagonal]
    rw [this, det_mul, det_diagonal, mul_comm, Finset.prod_pow_eq_pow_sum, Finset.sum_coe_sort s]
  have hunit : ∀ s : Finset (Fin r), IsUnit (U.submatrix (Subtype.val : s → Fin r) Subtype.val).det :=
    fun s => isUnit_det_of_isUnit_diag_of_dvd_lower hϖ _ (fun i => hU i) (fun i j h => hU' i j h)
  set T := univ.filter fun j : Fin r => r - k ≤ (j : ℕ)
  have hT : T ∈ powersetCard k (univ : Finset (Fin r)) :=
    mem_powersetCard.mpr ⟨subset_univ _, card_filter_sub_le_eq r k hk⟩
  rw [← add_sum_erase _ _ hT]
  have hrest : ϖ ^ (∑ j ∈ T, a j + 1) ∣ ∑ s ∈ (powersetCard k univ).erase T,
      ((U * diagonal fun i => ϖ ^ a i).submatrix (Subtype.val : s → Fin r) Subtype.val).det := by
    refine dvd_sum fun s hs => ?_
    rw [hminor]
    have hsT := ne_of_mem_erase hs
    have hcs : s.card = T.card := by
      rw [(mem_powersetCard.mp (mem_of_mem_erase hs)).2, card_filter_sub_le_eq r k hk]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (sum_filter_lt_sum_of_strictAnti ha k s hcs hsT)) _
  obtain ⟨c, hc'⟩ := hrest
  rw [hc', hminor, pow_succ, mul_assoc, ← mul_add]
  refine ⟨((isUnit_neg_one (α := O)).pow k |>.mul
    (isUnit_add_mul_of_mem_maximalIdeal hϖ (hunit T) c)).unit, ?_⟩
  simp only [IsUnit.unit_spec]
  ring

theorem premises_model :
    (2 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] ∧ (2 : ℤ_[2]) ≠ 0 ∧
    StrictAnti (![1, 0] : Fin 2 → ℕ) ∧
    (∀ i, IsUnit ((!![1, 1; 2, 1] : Matrix (Fin 2) (Fin 2) ℤ_[2]) i i)) ∧
    (∀ i j, j < i → (2 : ℤ_[2]) ∣ (!![1, 1; 2, 1] : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j) := by
  refine ⟨?_, two_ne_zero, by decide, ?_, ?_⟩
  · rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  · intro i; fin_cases i <;> simp
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all

end GlobalTheory.IwahoriNewtonTest
