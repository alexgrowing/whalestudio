import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenCol

open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

private theorem symplectic_sum_pair_eq_J {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hA : A ∈ symplecticGroup (Fin g) ℤ) (p q : Fin g ⊕ Fin g) :
    ∑ b, (A (Sum.inr b) p * A (Sum.inl b) q - A (Sum.inl b) p * A (Sum.inr b) q) =
      J (Fin g) ℤ p q := by
  have h := SymplecticGroup.transpose_mem hA
  rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at h
  rw [← h]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply]
  simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

private theorem symplectic_inl_inl_eq_zero_of_colsFixed {k : ℕ} {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hA : A ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k A) {i m : Fin g} (hi : (i : ℕ) < k)
    (hm : m ≠ i) : A (Sum.inl i) (Sum.inl m) = 0 := by
  have h := symplectic_sum_pair_eq_J hA (Sum.inr i) (Sum.inl m)
  obtain ⟨-, h2⟩ := hF i hi
  simpa [h2, Matrix.one_apply, Matrix.J, Matrix.fromBlocks, Ne.symm hm] using h

theorem phase2 (k : Fin g) (n : ℕ) : ∀ M ∈ symplecticGroup (Fin g) ℤ, ColsFixed k M →
    (∀ j, M (Sum.inr j) (Sum.inl k) = 0) → ∑ j, (M (Sum.inl j) (Sum.inl k)).natAbs = n →
    ∃ O ∈ spH g, ColsFixed k O ∧ (∀ j, (O * M) (Sum.inr j) (Sum.inl k) = 0) ∧
      ∀ i j, (O * M) (Sum.inl i) (Sum.inl k) ≠ 0 → (O * M) (Sum.inl j) (Sum.inl k) ≠ 0 → i = j := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM hF hbot hsum
  by_cases hone : ∀ i j, M (Sum.inl i) (Sum.inl k) ≠ 0 → M (Sum.inl j) (Sum.inl k) ≠ 0 → i = j
  · exact ⟨1, (spH g).one_mem, colsFixed_one _, by simpa using hbot, by simpa using hone⟩
  push_neg at hone
  obtain ⟨a, b, ha, hb, hab⟩ := hone
  wlog hle : (M (Sum.inl b) (Sum.inl k)).natAbs ≤ (M (Sum.inl a) (Sum.inl k)).natAbs generalizing a b
  · exact this b a hb ha (Ne.symm hab) (by omega)
  have hak : (k : ℕ) ≤ a := by
    by_contra hlt
    push_neg at hlt
    exact ha (symplectic_inl_inl_eq_zero_of_colsFixed hM hF hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  have hbk : (k : ℕ) ≤ b := by
    by_contra hlt
    push_neg at hlt
    exact hb (symplectic_inl_inl_eq_zero_of_colsFixed hM hF hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  let t : ℤ := M (Sum.inl a) (Sum.inl k) / M (Sum.inl b) (Sum.inl k)
  let E : Matrix (Fin g) (Fin g) ℤ :=
    Matrix.of fun c u => (if c = u then (1 : ℤ) else 0) - if c = a ∧ u = b then t else 0
  let E' : Matrix (Fin g) (Fin g) ℤ :=
    Matrix.of fun c u => (if c = u then (1 : ℤ) else 0) + if c = a ∧ u = b then t else 0
  have hEE' : E * E' = 1 := by
    ext c d
    simp [E, E', Matrix.mul_apply, Matrix.one_apply, sub_mul, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ite_and]
    split_ifs <;> simp_all
  have hE'E : E' * E = 1 := by
    ext c d
    simp [E, E', Matrix.mul_apply, Matrix.one_apply, add_mul, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ite_and]
    split_ifs <;> simp_all
  let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨E, E', hEE', hE'E⟩
  have hO1 : spDiag U ∈ spH g := spDiag_mem U
  have hF1 : ColsFixed k (spDiag U) := by
    intro i hi
    have hia : i ≠ a := fun h => by subst h; omega
    have hib : i ≠ b := fun h => by subst h; omega
    have e1 : ∀ c : Fin g, (i = c ↔ c = i) := fun c => eq_comm
    constructor <;> intro r <;> rcases r with c | c <;>
      simp [spDiag, U, E, E', Matrix.fromBlocks, Matrix.one_apply, hia, hib, e1]
  have hnew : ∀ c, (spDiag U * M) (Sum.inl c) (Sum.inl k) =
      M (Sum.inl c) (Sum.inl k) - if c = a then t * M (Sum.inl b) (Sum.inl k) else 0 := by
    intro c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp [spDiag, U, E, Matrix.fromBlocks, hbot, sub_mul, Finset.sum_sub_distrib, ite_and]
  have hbot1 : ∀ j, (spDiag U * M) (Sum.inr j) (Sum.inl k) = 0 := by
    intro j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp [spDiag, Matrix.fromBlocks, hbot]
  have hkey : (M (Sum.inl a) (Sum.inl k) - t * M (Sum.inl b) (Sum.inl k)).natAbs <
      (M (Sum.inl a) (Sum.inl k)).natAbs := by
    have he : M (Sum.inl a) (Sum.inl k) - t * M (Sum.inl b) (Sum.inl k) =
        M (Sum.inl a) (Sum.inl k) % M (Sum.inl b) (Sum.inl k) := by
      rw [Int.emod_def]
      ring
    have h1 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (M (Sum.inl a) (Sum.inl k)) hb)
      (Int.emod_lt (M (Sum.inl a) (Sum.inl k)) hb)
    have h2 : (M (Sum.inl a) (Sum.inl k) % M (Sum.inl b) (Sum.inl k)).natAbs <
        (M (Sum.inl b) (Sum.inl k)).natAbs := by
      simp only [Int.natCast_natAbs] at h1
      rwa [Int.natAbs_abs] at h1
    rw [he]
    omega
  have hlt : ∑ j, ((spDiag U * M) (Sum.inl j) (Sum.inl k)).natAbs < n := by
    rw [← hsum]
    apply Finset.sum_lt_sum
    · intro j _
      rw [hnew]
      by_cases hja : j = a
      · subst hja
        simp only [if_true]
        exact hkey.le
      · simp [hja]
    · exact ⟨a, Finset.mem_univ _, by rw [hnew]; simpa using hkey⟩
  have hM1 : spDiag U * M ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO1) hM
  obtain ⟨O2, hO2, hF2, hb2, hone2⟩ := ih _ hlt (spDiag U * M) hM1 (colsFixed_mul hF1 hF) hbot1 rfl
  refine ⟨O2 * spDiag U, (spH g).mul_mem hO2 hO1, colsFixed_mul hF2 hF1, ?_, ?_⟩
  · simpa [Matrix.mul_assoc] using hb2
  · simpa [Matrix.mul_assoc] using hone2

theorem move_col (k j : Fin g) (hjk : (k : ℕ) ≤ j) (hne : j ≠ k) (s : ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl j then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r, (O * M) r (Sum.inl k) = if r = Sum.inl k then s else 0 := by
  classical
  let P : Matrix (Fin g) (Fin g) ℤ := Matrix.of fun a b => if Equiv.swap j k a = b then 1 else 0
  have hP : P * P = 1 := by
    ext a b
    simp only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (Equiv.swap j k a)]
    · simp [Equiv.swap_apply_self, eq_comm]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨P, P, hP, hP⟩
  refine ⟨spDiag U, spDiag_mem U, fun i hi => ?_, fun r => ?_⟩
  · have hik : i ≠ k := fun h => by subst h; exact lt_irrefl _ hi
    have hij : i ≠ j := fun h => by subst h; omega
    have hsw : Equiv.swap j k i = i := Equiv.swap_apply_of_ne_of_ne hij hik
    constructor <;> intro r <;> rcases r with a | a
    · have h1 : (Equiv.swap j k a = i) ↔ (a = i) := by rw [Equiv.swap_apply_eq_iff, hsw]
      simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks, h1]
    · simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks]
    · simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks]
    · have h1 : (i = a) ↔ (a = i) := eq_comm
      simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks, Matrix.transpose_apply, hsw, h1]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with a | a <;>
      simp [spDiag, U, P, hsupp, Matrix.one_apply, Matrix.fromBlocks, Equiv.swap_apply_eq_iff] <;>
      try (split_ifs <;> simp_all)

theorem sign_col (k : Fin g) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl k then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r,
      (O * M) r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
  classical
  rcases hs with rfl | rfl
  · refine ⟨1, (spH g).one_mem, colsFixed_one _, fun r => ?_⟩
    rw [Matrix.one_mul, hsupp r, Matrix.one_apply]
  · let D : Matrix (Fin g) (Fin g) ℤ := Matrix.diagonal fun i => if i = k then -1 else 1
    have hD : D * D = 1 := by
      simp only [D, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      split_ifs <;> norm_num
    let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨D, D, hD, hD⟩
    refine ⟨spDiag U, spDiag_mem U, fun i hi => ?_, fun r => ?_⟩
    · have hik : i ≠ k := fun h => by subst h; exact lt_irrefl _ hi
      constructor <;> intro r <;> rcases r with a | a <;>
        simp [spDiag, U, D, Matrix.one_apply, Matrix.diagonal_apply, Matrix.fromBlocks] <;>
        split_ifs <;> simp_all
    · rw [Matrix.mul_apply, Fintype.sum_sum_type]
      rcases r with a | a <;>
        simp [spDiag, U, D, hsupp, Matrix.one_apply, Matrix.diagonal_apply, Matrix.fromBlocks] <;>
        split_ifs <;> simp_all

theorem col_inl_step (k : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r,
      (O * M) r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
  classical
  obtain ⟨O1, hO1, hF1, hb1⟩ := phase1 k _ M hM hF rfl
  have hM1 : O1 * M ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO1) hM
  obtain ⟨O2, hO2, hF2, hb2, hone2⟩ := phase2 k _ (O1 * M) hM1 (colsFixed_mul hF1 hF) hb1 rfl
  have hA : O2 * (O1 * M) ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO2) hM1
  have hFA : ColsFixed k (O2 * (O1 * M)) := colsFixed_mul hF2 (colsFixed_mul hF1 hF)
  have hid := symplectic_sum_pair_eq_J hA (Sum.inl k) (Sum.inr k)
  simp only [hb2, zero_mul, zero_sub] at hid
  simp [Matrix.J, Matrix.fromBlocks, Finset.sum_neg_distrib] at hid
  obtain ⟨j, hj⟩ : ∃ j, (O2 * (O1 * M)) (Sum.inl j) (Sum.inl k) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    simp [hcon] at hid
  have hz : ∀ c, c ≠ j → (O2 * (O1 * M)) (Sum.inl c) (Sum.inl k) = 0 := by
    intro c hc
    by_contra h
    exact hc (hone2 c j h hj)
  have hsupp : ∀ r, (O2 * (O1 * M)) r (Sum.inl k) =
      if r = Sum.inl j then (O2 * (O1 * M)) (Sum.inl j) (Sum.inl k) else 0 := by
    intro r
    rcases r with c | c
    · by_cases hc : c = j
      · subst hc
        simp
      · simp [hc, hz c hc]
    · simp [hb2]
  rw [Finset.sum_eq_single j (fun c _ hc => by rw [hz c hc, zero_mul]) (by simp)] at hid
  have hs := Int.eq_one_or_neg_one_of_mul_eq_one hid
  have hjk : (k : ℕ) ≤ j := by
    by_contra hlt
    push_neg at hlt
    exact hj (symplectic_inl_inl_eq_zero_of_colsFixed hA hFA hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  rcases eq_or_ne j k with hjk' | hjk'
  · rw [hjk'] at hsupp hs
    obtain ⟨O3, hO3, hF3, h3⟩ := sign_col k _ hs _ hsupp
    refine ⟨O3 * O2 * O1, (spH g).mul_mem ((spH g).mul_mem hO3 hO2) hO1,
      colsFixed_mul (colsFixed_mul hF3 hF2) hF1, fun r => ?_⟩
    simpa [Matrix.mul_assoc] using h3 r
  · obtain ⟨O3, hO3, hF3, h3⟩ := move_col k j hjk hjk' _ _ hsupp
    obtain ⟨O4, hO4, hF4, h4⟩ := sign_col k _ hs _ h3
    refine ⟨O4 * O3 * O2 * O1, (spH g).mul_mem ((spH g).mul_mem ((spH g).mul_mem hO4 hO3) hO2) hO1,
      colsFixed_mul (colsFixed_mul (colsFixed_mul hF4 hF3) hF2) hF1, fun r => ?_⟩
    simpa [Matrix.mul_assoc] using h4 r

end ReciprocityTheory.ChartRestriction.G.Key.Chi
