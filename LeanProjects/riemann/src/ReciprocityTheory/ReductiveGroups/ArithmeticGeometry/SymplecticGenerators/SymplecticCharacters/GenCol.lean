import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenBase

open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

def ColsFixed (k : ℕ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ i : Fin g, (i : ℕ) < k →
    (∀ r, M r (Sum.inl i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl i)) ∧
    (∀ r, M r (Sum.inr i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr i))

theorem colsFixed_one (k : ℕ) : ColsFixed k (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
  intro i _
  exact ⟨fun r => rfl, fun r => rfl⟩

theorem colsFixed_mul {k : ℕ} {O M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hO : ColsFixed k O) (hM : ColsFixed k M) : ColsFixed k (O * M) := by
  intro i hi
  refine ⟨fun r => ?_, fun r => ?_⟩
  · have e : (O * M) r (Sum.inl i) = (O * (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) r (Sum.inl i) := by
      simp only [Matrix.mul_apply, (hM i hi).1]
    rw [e, Matrix.mul_one, (hO i hi).1]
  · have e : (O * M) r (Sum.inr i) = (O * (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) r (Sum.inr i) := by
      simp only [Matrix.mul_apply, (hM i hi).2]
    rw [e, Matrix.mul_one, (hO i hi).2]

private theorem J_mul_apply_inl (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (j : Fin g)
    (q : Fin g ⊕ Fin g) : (J (Fin g) ℤ * M) (Sum.inl j) q = -M (Sum.inr j) q := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem symplectic_entry_mul_J_mul_of_single_column_entry {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {p r0 : Fin g ⊕ Fin g} (h : ∀ r, r ≠ r0 → M r p = 0)
    (q : Fin g ⊕ Fin g) : M r0 p * (J (Fin g) ℤ * M) r0 q = J (Fin g) ℤ p q := by
  have h1 := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem hM)
  rw [Matrix.transpose_transpose, Matrix.mul_assoc] at h1
  have h2 := congrArg (fun A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ => A p q) h1
  rw [Matrix.mul_apply, Finset.sum_eq_single r0] at h2
  · rw [Matrix.transpose_apply] at h2
    exact h2
  · intro r _ hr
    rw [Matrix.transpose_apply, h r hr, zero_mul]
  · intro hr
    exact absurd (Finset.mem_univ _) hr

theorem low_entries {k : ℕ} {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M) {i j : Fin g} (hi : (i : ℕ) < k)
    (hj : k ≤ (j : ℕ)) : M (Sum.inl i) (Sum.inl j) = 0 ∧ M (Sum.inr i) (Sum.inl j) = 0 := by
  have hi1 := hF i hi
  have hA : ∀ r, r ≠ Sum.inl i → M r (Sum.inl i) = 0 := fun r hr => by
    rw [hi1.1 r, Matrix.one_apply_ne hr]
  have hB : ∀ r, r ≠ Sum.inr i → M r (Sum.inr i) = 0 := fun r hr => by
    rw [hi1.2 r, Matrix.one_apply_ne hr]
  have hA1 : M (Sum.inl i) (Sum.inl i) = 1 := by rw [hi1.1, Matrix.one_apply_eq]
  have hB1 : M (Sum.inr i) (Sum.inr i) = 1 := by rw [hi1.2, Matrix.one_apply_eq]
  have hij : i ≠ j := fun h => by subst h; omega
  have e1 := symplectic_entry_mul_J_mul_of_single_column_entry hM hA (Sum.inl j)
  have e2 := symplectic_entry_mul_J_mul_of_single_column_entry hM hB (Sum.inl j)
  rw [hA1, one_mul, J_mul_apply_inl] at e1
  rw [hB1, one_mul] at e2
  constructor
  · simpa [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hij] using e2
  · simpa [Matrix.J] using e1

theorem J_mul_inl (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (j : Fin g) (q : Fin g ⊕ Fin g) :
    (J (Fin g) ℤ * M) (Sum.inl j) q = -M (Sum.inr j) q := by
  exact J_mul_apply_inl M j q

theorem col_single_entry {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {p r0 : Fin g ⊕ Fin g} (h : ∀ r, r ≠ r0 → M r p = 0)
    (q : Fin g ⊕ Fin g) : M r0 p * (J (Fin g) ℤ * M) r0 q = J (Fin g) ℤ p q := by
  exact symplectic_entry_mul_J_mul_of_single_column_entry hM h q

theorem eJ_apply (j i l : Fin g) : eJ j i l = if j = i ∧ j = l then 1 else 0 := rfl

theorem sum_eJ (j i : Fin g) (x : Fin g → ℤ) :
    ∑ l, eJ j i l * x l = if i = j then x j else 0 := by
  simp only [eJ_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Ne.symm h, h]

theorem spTransl_mul_inl (S : Matrix (Fin g) (Fin g) ℤ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spTransl S * M) (Sum.inl i) p = M (Sum.inl i) p + ∑ l, S i l * M (Sum.inr l) p := by
  simp [spTransl, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem spTransl_mul_inr (S : Matrix (Fin g) (Fin g) ℤ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (i : Fin g) (p : Fin g ⊕ Fin g) : (spTransl S * M) (Sum.inr i) p = M (Sum.inr i) p := by
  simp [spTransl, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem spPJ_mul_inl (j : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g)
    (p : Fin g ⊕ Fin g) :
    (spPJ j * M) (Sum.inl i) p = if i = j then M (Sum.inr j) p else M (Sum.inl i) p := by
  simp only [spPJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, sum_eJ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  split_ifs with h
  · subst h
    ring
  · ring

theorem spPJ_mul_inr (j : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g)
    (p : Fin g ⊕ Fin g) :
    (spPJ j * M) (Sum.inr i) p = if i = j then -M (Sum.inl j) p else M (Sum.inr i) p := by
  simp only [spPJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.neg_apply, sub_mul, neg_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, sum_eJ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  split_ifs with h
  · subst h
    ring
  · ring

theorem colsFixed_spTransl {k : ℕ} {S : Matrix (Fin g) (Fin g) ℤ}
    (hS : ∀ i : Fin g, (i : ℕ) < k → ∀ l, S l i = 0) : ColsFixed k (spTransl S) := by
  intro i hi
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [spTransl, Matrix.one_apply, hS i hi]

theorem colsFixed_spPJ {k : ℕ} (j : Fin g) (hj : k ≤ (j : ℕ)) : ColsFixed k (spPJ j) := by
  intro i hi
  have hij : j ≠ i := fun h => by subst h; omega
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [spPJ, Matrix.single_apply, Matrix.one_apply, hij]

theorem vecMulVec_sq {u v : Fin g → ℤ} (h : v ⬝ᵥ u = 0) : vecMulVec u v * vecMulVec u v = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  have e : ∑ l, u a * v l * (u l * v b) = u a * v b * (v ⬝ᵥ u) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e, h, mul_zero]

def rkU (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) : (Matrix (Fin g) (Fin g) ℤ)ˣ where
  val := 1 + vecMulVec u v
  inv := 1 - vecMulVec u v
  val_inv := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, vecMulVec_sq h]; abel
  inv_val := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, vecMulVec_sq h]; abel

theorem rkU_val (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) :
    ((rkU u v h : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) = 1 + vecMulVec u v := rfl

theorem rkU_inv_val (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) :
    (((rkU u v h)⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) =
      1 - vecMulVec u v := rfl

theorem spDiag_rk_mul_inl (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spDiag (rkU u v h) * M) (Sum.inl i) p = M (Sum.inl i) p + u i * ∑ l, v l * M (Sum.inl l) p := by
  simp only [spDiag, rkU_val, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => by ring)

theorem spDiag_rk_mul_inr (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (spDiag (rkU u v h) * M) (Sum.inr i) p = M (Sum.inr i) p - v i * ∑ l, u l * M (Sum.inr l) p := by
  simp only [spDiag, rkU_inv_val, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => by ring)

theorem colsFixed_spDiag_rk {k : ℕ} {u v : Fin g → ℤ} (h : v ⬝ᵥ u = 0)
    (hu : ∀ i : Fin g, (i : ℕ) < k → u i = 0) (hv : ∀ i : Fin g, (i : ℕ) < k → v i = 0) :
    ColsFixed k (spDiag (rkU u v h)) := by
  intro i hi
  simp only [spDiag, rkU_val, rkU_inv_val]
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [Matrix.vecMulVec_apply, hu i hi, hv i hi, Matrix.one_apply, eq_comm]

theorem phase1 (k : Fin g) (n : ℕ) : ∀ M ∈ symplecticGroup (Fin g) ℤ, ColsFixed k M →
    ∑ j, (M (Sum.inr j) (Sum.inl k)).natAbs = n →
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ j, (O * M) (Sum.inr j) (Sum.inl k) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro M hM hF hn
  by_cases hb : ∀ j, M (Sum.inr j) (Sum.inl k) = 0
  · exact ⟨1, Submonoid.one_mem _, colsFixed_one _, fun j => by rw [Matrix.one_mul]; exact hb j⟩
  push_neg at hb
  obtain ⟨j0, hd⟩ := hb
  have hkj0 : (k : ℕ) ≤ (j0 : ℕ) := by
    by_contra hlt
    exact hd (low_entries hM hF (not_le.mp hlt) le_rfl).2
  set a := M (Sum.inl j0) (Sum.inl k) with ha
  set d := M (Sum.inr j0) (Sum.inl k) with hdd
  set S : Matrix (Fin g) (Fin g) ℤ := (-(a / d)) • eJ j0 with hS
  have hSsymm : S.IsSymm := by
    simp [hS, Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_single]
  have hSk : ∀ i : Fin g, (i : ℕ) < k → ∀ l, S l i = 0 := by
    intro i hi l
    have hne : j0 ≠ i := fun h => by subst h; omega
    simp [hS, Matrix.single_apply, hne]
  have hO1 : spPJ j0 * spTransl S ∈ spH g := Submonoid.mul_mem _ (spPJ_mem j0) (spTransl_mem hSsymm)
  have hspH : spH g ≤ symplecticGroup (Fin g) ℤ := Submonoid.closure_le.2 (spGens_subset g)
  have hM' : spPJ j0 * spTransl S * M ∈ symplecticGroup (Fin g) ℤ :=
    Submonoid.mul_mem _ (hspH hO1) hM
  have hF' : ColsFixed k (spPJ j0 * spTransl S * M) :=
    colsFixed_mul (colsFixed_mul (colsFixed_spPJ j0 hkj0) (colsFixed_spTransl hSk)) hF
  have hkey : (a % d).natAbs < d.natAbs := by
    have h1 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg a hd) (Int.emod_lt a hd)
    rwa [Int.natAbs_cast] at h1
  have hrow : ∀ j, (spPJ j0 * spTransl S * M) (Sum.inr j) (Sum.inl k) =
      if j = j0 then -(a % d) else M (Sum.inr j) (Sum.inl k) := by
    intro j
    rw [Matrix.mul_assoc, spPJ_mul_inr, spTransl_mul_inl, spTransl_mul_inr]
    split_ifs with hj
    · congr 1
      have e : ∑ l, S j0 l * M (Sum.inr l) (Sum.inl k) = -(a / d) * d := by
        simp only [hS, Matrix.smul_apply, smul_eq_mul, mul_assoc]
        rw [← Finset.mul_sum, sum_eJ, if_pos rfl]
      rw [e, Int.emod_def]
      ring
    · rfl
  have hlt : ∑ j, ((spPJ j0 * spTransl S * M) (Sum.inr j) (Sum.inl k)).natAbs < n := by
    rw [← hn]
    apply Finset.sum_lt_sum
    · intro j _
      rw [hrow j]
      split_ifs with hj
      · subst hj
        rw [Int.natAbs_neg]
        exact hkey.le
      · exact le_rfl
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      rw [hrow j0, if_pos rfl, Int.natAbs_neg]
      exact hkey
  obtain ⟨O2, hO2, hF2, h2⟩ := ih _ hlt _ hM' hF' rfl
  refine ⟨O2 * (spPJ j0 * spTransl S), Submonoid.mul_mem _ hO2 hO1, colsFixed_mul hF2
    (colsFixed_mul (colsFixed_spPJ j0 hkj0) (colsFixed_spTransl hSk)), fun j => ?_⟩
  rw [Matrix.mul_assoc]
  exact h2 j

end ReciprocityTheory.ChartRestriction.G.Key.Chi
