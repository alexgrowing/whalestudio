import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def LowZ {n : ℕ} {R : Type} [CommRing R] (r : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0

private theorem LowZ.mul {n r : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : LowZ r M) (hN : LowZ r N) : LowZ r (M * N) := fun i j hi hj => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (k : ℕ) r with hk | hk
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j hk hj, mul_zero]

private theorem lower_zero_first_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin r) R) :
    LowZ r (emb (e1 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, extendByZero_apply_eq_zero_of_row_not_mem, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem lower_zero_second_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin s) R) :
    LowZ r (emb (e2 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, matrixExtendByZero_apply_of_outside_col, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem blockEntry_eq_sum {n r : ℕ} {S : Type} [CommRing S] (Y : UPos n r → S) :
    blockEntry Y = ∑ q : UPos n r, Matrix.single q.1.1 q.1.2 (Y q) := by
  ext i j
  rw [blockEntry_apply, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(i, j), h⟩ : UPos n r)]
    · simp
    · intro q _ hq
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hq rfl
    · simp
  · symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h q.2

private theorem conj_blockEntry {n r : ℕ} {S : Type} [CommRing S] {M N : Matrix (Fin n) (Fin n) S}
    (hM : LowZ r M) (hN : LowZ r N) (Y : UPos n r → S) :
    M * blockEntry Y * N = blockEntry (fun p : UPos n r => ∑ q : UPos n r, M p.1.1 q.1.1 * N q.1.2 p.1.2 * Y q) := by
  ext i j
  have h0 : (M * blockEntry Y * N) i j = ∑ q : UPos n r, M i q.1.1 * N q.1.2 j * Y q := by
    rw [blockEntry_eq_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_zero, ite_and, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ite_mul, zero_mul]
    ring
  rw [h0, blockEntry_apply]
  split_ifs with h
  · rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    rcases lt_or_ge (i : ℕ) r with hi | hi
    · rw [hN _ j q.2.2 (by omega), mul_zero, zero_mul]
    · rw [hM i _ hi q.2.1, zero_mul, zero_mul]

theorem UpperTheory.blockDiag_conj_unipotent_linear :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), ∃ c : UPos (r + s) r → UPos (r + s) r → R, ∀ (S : Type) [CommRing S] (f : R →+* S) (Y : UPos (r + s) r → S), Matrix.GeneralLinearGroup.map f (blk m₁ m₂) * unipGL Y = unipGL (fun p => ∑ q, f (c p q) * Y q) * Matrix.GeneralLinearGroup.map f (blk m₁ m₂) := by
  intro R _ r s m₁ m₂
  have h1 : LowZ r (blk m₁ m₂).val := (lower_zero_first_block_embedding m₁).mul (lower_zero_second_block_embedding m₂)
  have h2 : LowZ r ((blk m₁ m₂)⁻¹).val := by
    rw [blk, _root_.mul_inv_rev, ← map_inv, ← map_inv]
    exact (lower_zero_second_block_embedding _).mul (lower_zero_first_block_embedding _)
  generalize blk m₁ m₂ = m at h1 h2
  refine ⟨fun p q => m.val p.1.1 q.1.1 * (m⁻¹).val q.1.2 p.1.2, fun S _ f Y => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← map_inv]
  refine Units.ext ?_
  have hmm : m.val.map f * (m⁻¹).val.map f = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
  have h1' : LowZ r (m.val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h1 i j hi hj, map_zero]
  have h2' : LowZ r ((m⁻¹).val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h2 i j hi hj, map_zero]
  change m.val.map f * (1 + blockEntry Y) * (m⁻¹).val.map f = 1 + blockEntry _
  rw [mul_add, add_mul, mul_one, hmm, conj_blockEntry h1' h2']
  simp only [Matrix.map_apply, map_mul]
