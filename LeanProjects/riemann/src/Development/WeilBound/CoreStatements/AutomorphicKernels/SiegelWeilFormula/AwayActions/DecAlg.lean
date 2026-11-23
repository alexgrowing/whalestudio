import Mathlib

noncomputable section

open scoped Matrix
open Matrix

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {R : Type} [CommRing R] {n : ℕ}

def jF (n : ℕ) (ε : ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks 0 1 ((ε : R) • 1) 0

def nM (t : Matrix (Fin n) (Fin n) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks 1 t 0 1

variable (c : R →+* R) (ε : ℤ)

theorem nM_cond_iff (t : Matrix (Fin n) (Fin n) R) :
    (nM t)ᵀ * jF n ε * (nM t).map c = jF n ε ↔ tᵀ + (ε : R) • t.map c = 0 := by
  simp only [nM, jF, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_inj]
  simp [Matrix.map_one c (map_zero c) (map_one c), add_comm]

theorem upper_block_rank_one_update (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hM : Mᵀ * jF n ε * M.map c = jF n ε) :
    (M.toBlocks₁₁)ᵀ * (M.toBlocks₂₁).map c + (ε : R) • ((M.toBlocks₂₁)ᵀ * (M.toBlocks₁₁).map c) = 0 := by
  have hM' := hM
  rw [← fromBlocks_toBlocks M] at hM'
  simp only [jF, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_inj] at hM'
  have h := hM'.1
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, zero_add, add_zero] at h
  rw [add_comm]
  exact h

theorem blkUpper (A B D : Matrix (Fin n) (Fin n) R) (hM : (fromBlocks A B 0 D)ᵀ * jF n ε * (fromBlocks A B 0 D).map c = jF n ε) :
    Aᵀ * D.map c = 1 ∧ Bᵀ * D.map c + (ε : R) • (Dᵀ * B.map c) = 0 := by
  simp only [jF, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_inj] at hM
  obtain ⟨-, h12, -, h22⟩ := hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, zero_add,
    add_zero, transpose_zero, smul_zero] at h12 h22
  exact ⟨h12, by rw [add_comm]; exact h22⟩

theorem det_idem_sum {ι : Type} [Fintype ι] (f : ι → R) (hf : ∀ i, f i * f i = f i) (ho : ∀ i j, i ≠ j → f i * f j = 0)
    (h1 : ∑ i, f i = 1) (M : ι → Matrix (Fin n) (Fin n) R) : (∑ i, f i • M i).det = ∑ i, f i * (M i).det := by
  cases n with
  | zero => simp [Matrix.det_fin_zero, h1]
  | succ m =>
    have hX : ∀ i, f i • (∑ j, f j • M j) = f i • M i := by
      intro i
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, hf]
      · intro j _ hj
        rw [smul_smul, ho i j (Ne.symm hj), zero_smul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hd : ∀ i (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R), (f i • Y).det = f i * Y.det := by
      intro i Y
      rw [Matrix.det_smul, Fintype.card_fin, IsIdempotentElem.pow_succ_eq m (hf i)]
    calc (∑ i, f i • M i).det = (∑ i, f i) * (∑ i, f i • M i).det := by rw [h1, one_mul]
      _ = ∑ i, f i * (∑ j, f j • M j).det := Finset.sum_mul _ _ _
      _ = ∑ i, f i * (M i).det := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hd, hX, hd]

theorem exists_T_field {K : Type} [Field K] [Infinite K] (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hX : X.det ≠ 0) :
    ∃ T : Matrix (Fin n) (Fin n) K, (X.toBlocks₁₁ - T * X.toBlocks₂₁).det ≠ 0 := by
  classical
  set A := X.toBlocks₁₁ with hA
  set C := X.toBlocks₂₁ with hC
  have hZX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hX)
  set P := (X⁻¹).toBlocks₁₁ with hP
  set Q := (X⁻¹).toBlocks₁₂ with hQ
  have hPQ : P * A + Q * C = 1 := by
    ext i j
    have h := congrFun (congrFun hZX (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hA, hC, hP, hQ, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using h
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (insert 0 ((-P).charpoly.roots.toFinset ∪ (-A).charpoly.roots.toFinset.image (·⁻¹)))
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  have hsP : (Matrix.scalar (Fin n) s - -P).det ≠ 0 := by
    intro h
    apply hs
    refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    exact (Matrix.eval_charpoly _ _).trans h
  have hsA : (Matrix.scalar (Fin n) s⁻¹ - -A).det ≠ 0 := by
    intro h
    apply hs
    refine Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨s⁻¹, ?_, inv_inv s⟩))
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    exact (Matrix.eval_charpoly _ _).trans h
  set U := Matrix.scalar (Fin n) s - -P with hU
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hsP
  refine ⟨-(U⁻¹ * Q), ?_⟩
  have hUA : U * A = s • A + P * A := by
    rw [hU, sub_neg_eq_add, Matrix.add_mul]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul]
  have key : U * (A - -(U⁻¹ * Q) * C) = s • (Matrix.scalar (Fin n) s⁻¹ - -A) := by
    rw [neg_mul, sub_neg_eq_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hUu, Matrix.one_mul, hUA, add_assoc, hPQ]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> field_simp <;> ring
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul] at this
  exact mul_ne_zero (pow_ne_zero _ hs0) hsA this.symm

theorem cond_c (A C : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) (hε : ε * ε = 1)
    (h : Aᵀ * C.map c + (ε : R) • (Cᵀ * A.map c) = 0) (ε₁ : ℤ) :
    ((ε₁ : R) • (C * A⁻¹))ᵀ + (ε : R) • ((ε₁ : R) • (C * A⁻¹)).map c = 0 := by
  have hP : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have hQdet : (A.map c).det = c A.det := (RingHom.map_det c A).symm
  have hQ : IsUnit (A.map c).det := by rw [hQdet]; exact hA.map c
  have hinv : (A.map c)⁻¹ = (A⁻¹).map c := Matrix.inv_eq_left_inv (by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one c (map_zero c) (map_one c)])
  have hεR : (ε : R) * (ε : R) = 1 := by rw [← Int.cast_mul, hε, Int.cast_one]
  have key : (C * A⁻¹)ᵀ + (ε : R) • (C * A⁻¹).map c = 0 := by
    rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.transpose_nonsing_inv, ← hinv]
    have hcancel : ∀ Z : Matrix (Fin n) (Fin n) R, Aᵀ * Z * A.map c = 0 → Z = 0 := by
      intro Z hZ
      calc Z = (Aᵀ)⁻¹ * (Aᵀ * Z * A.map c) * (A.map c)⁻¹ := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul,
              Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]
        _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
    apply hcancel
    have e1 : Aᵀ * ((Aᵀ)⁻¹ * Cᵀ) * A.map c = Cᵀ * A.map c := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.one_mul]
    have e2 : Aᵀ * (C.map c * (A.map c)⁻¹) * A.map c = Aᵀ * C.map c := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e1, e2,
      eq_neg_of_add_eq_zero_left h, smul_neg, smul_smul, hεR, one_smul, add_neg_cancel]
  have hc1 : c (ε₁ : R) = (ε₁ : R) := map_intCast c ε₁
  rw [Matrix.transpose_smul, Matrix.map_smul' c _ _ (map_mul c), hc1, smul_comm (ε : R) (ε₁ : R), ← smul_add,
    key, smul_zero]

theorem cond_b (hc : ∀ z, c (c z) = z) (A B D : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) (h1 : Aᵀ * D.map c = 1)
    (h2 : Bᵀ * D.map c + (ε : R) • (Dᵀ * B.map c) = 0) : (A⁻¹ * B)ᵀ + (ε : R) • (A⁻¹ * B).map c = 0 := by
  have hinv : (A.map c)⁻¹ = (A⁻¹).map c := Matrix.inv_eq_left_inv (by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one c (map_zero c) (map_one c)])
  have hT : (Aᵀ)⁻¹ = D.map c := Matrix.inv_eq_right_inv h1
  have hcc : (D.map c).map c = D := by
    rw [Matrix.map_map]
    ext i j
    exact hc (D i j)
  have hD : Dᵀ * A.map c = 1 := by
    have h1' := congrArg (fun M : Matrix (Fin n) (Fin n) R => (M.map c)ᵀ) h1
    simp only [Matrix.map_mul, Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.map_one c (map_zero c) (map_one c), Matrix.transpose_one] at h1'
    exact h1'
  have hDi : (A.map c)⁻¹ = Dᵀ := Matrix.inv_eq_left_inv hD
  rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.transpose_nonsing_inv, hT, ← hinv, hDi]
  exact h2

end PositivityTheory.SiegelWeilFormula.KAway

end
