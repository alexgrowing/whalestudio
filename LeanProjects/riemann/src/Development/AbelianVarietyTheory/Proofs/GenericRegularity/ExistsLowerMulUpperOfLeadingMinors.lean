import Mathlib

namespace GlobalTheory

open Matrix

section Cell
variable {R : Type} [CommRing R]

theorem det_eq_one_of_lower_unitriangular {r : ℕ} (l : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => h0 i j h)]
  simp [h1]

theorem exists_lower_mul_upper_of_leading_minors (r : ℕ) (h : Matrix (Fin r) (Fin r) R)
    (hm : ∀ k (hk : k ≤ r), IsUnit (h.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ l b : Matrix (Fin r) (Fin r) R, (∀ i j : Fin r, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      b.BlockTriangular id ∧ h = l * b := by
  induction r with
  | zero => exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩
  | succ r ih =>
    obtain ⟨L, B, hL0, hL1, hB, hA⟩ := ih (h.submatrix Fin.castSucc Fin.castSucc)
      (fun k hk => hm k (hk.trans (Nat.le_succ r)))
    have hLd : L.det = 1 := det_eq_one_of_lower_unitriangular L hL0 hL1
    have hAu : IsUnit (h.submatrix Fin.castSucc Fin.castSucc).det := hm r (Nat.le_succ r)
    have hBu : IsUnit B.det := by
      rw [hA, Matrix.det_mul, hLd, one_mul] at hAu; exact hAu
    have hLu : IsUnit L.det := by rw [hLd]; exact isUnit_one
    set x : Fin r → R := (fun j => h (Fin.last r) j.castSucc) ᵥ* B⁻¹ with hx
    set y : Fin r → R := L⁻¹ *ᵥ (fun i => h i.castSucc (Fin.last r)) with hy
    have hxB : x ᵥ* B = fun j => h (Fin.last r) j.castSucc := by
      rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hBu, Matrix.vecMul_one]
    have hLy : L *ᵥ y = fun i => h i.castSucc (Fin.last r) := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hLu, Matrix.one_mulVec]
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 x j)
        (fun i => Fin.lastCases (motive := fun _ => R) 0 (L i) j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) (h (Fin.last r) (Fin.last r) - x ⬝ᵥ y) (fun _ => 0) j)
        (fun i => Fin.lastCases (motive := fun _ => R) (y i) (B i) j) i, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hL0 i j (by simpa using hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hL1 i
    · intro i j hij
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last i))
      | cast j =>
        induction i using Fin.lastCases with
        | last => simp
        | cast i => simpa using hB (i := i) (j := j) (by simpa using hij)
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [dotProduct]
        | cast j => simpa [Matrix.vecMul, dotProduct] using (congrFun hxB j).symm
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa [Matrix.mulVec, dotProduct] using (congrFun hLy i).symm
        | cast j => simpa [Matrix.mul_apply] using congrFun (congrFun hA i) j

theorem eq_one_of_lower_unitriangular_eq_mul {r : ℕ} (l l' c : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (h0' : ∀ i j : Fin r, i < j → l' i j = 0) (h1' : ∀ i, l' i i = 1)
    (hc : c.BlockTriangular id) (h : l = l' * c) : c = 1 := by
  have key : ∀ i : Fin r, ∀ j, c i j = (1 : Matrix (Fin r) (Fin r) R) i j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro j
      rcases lt_or_ge j i with hji | hij
      · rw [hc hji, Matrix.one_apply_ne hji.ne']
      · have e : l i j = c i j := by
          rw [h, Matrix.mul_apply, Finset.sum_eq_single i, h1', one_mul]
          · intro k _ hk
            rcases lt_or_gt_of_ne hk with hk | hk
            · rw [ih k hk, Matrix.one_apply_ne (hk.trans_le hij).ne, mul_zero]
            · rw [h0' i k hk, zero_mul]
          · simp
        rw [← e]
        rcases hij.eq_or_lt with rfl | hij
        · simp [h1]
        · rw [h0 i j hij, Matrix.one_apply_ne hij.ne]
  ext i j
  exact key i j

theorem isUnit_det_of_upper_of_isUnit_diag {r : ℕ} (b : Matrix (Fin r) (Fin r) R)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) : IsUnit b.det := by
  rw [Matrix.det_of_upperTriangular hb]
  exact IsUnit.prod_iff.2 fun i _ => hu i

end Cell

theorem cell_coordinates_exists_unique :
    ∀ (R : Type) [CommRing R] (n r : ℕ) (ι : Fin r ↪ Fin n) (g : Matrix (Fin n) (Fin r) R), ((∀ k (hk : k ≤ r), IsUnit (g.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk)).det) ↔ ∃ (u : Matrix (Fin n) (Fin r) R) (b : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b) ∧ ∀ (u u' : Matrix (Fin n) (Fin r) R) (b b' : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ i j : Fin r, i < j → u' (ι i) j = 0) ∧ (∀ i : Fin r, u' (ι i) i = 1) → b.BlockTriangular id → b'.BlockTriangular id → (∀ i, IsUnit (b i i)) → u * b = u' * b' → u = u' ∧ b = b' := by
  intro R _ n r ι g
  refine ⟨⟨fun hm => ?_, ?_⟩, ?_⟩
  · obtain ⟨l, b, hl0, hl1, hb, hh⟩ :=
      exists_lower_mul_upper_of_leading_minors r (g.submatrix ι id) hm
    have hbu : IsUnit b.det := by
      have h1 : IsUnit (g.submatrix ι id).det := hm r le_rfl
      rwa [hh, Matrix.det_mul, det_eq_one_of_lower_unitriangular l hl0 hl1, one_mul] at h1
    have hu : ∀ i j, (g * b⁻¹) (ι i) j = l i j := by
      intro i j
      have : l = g.submatrix ι id * b⁻¹ := by
        rw [hh, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hbu, Matrix.mul_one]
      rw [this]; simp [Matrix.mul_apply]
    refine ⟨g * b⁻¹, b, fun i j hij => by rw [hu, hl0 i j hij], fun i => by rw [hu, hl1], hb, ?_, ?_⟩
    · intro i
      rw [Matrix.det_of_upperTriangular hb] at hbu
      exact IsUnit.prod_iff.1 hbu i (Finset.mem_univ _)
    · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbu, Matrix.mul_one]
  · rintro ⟨u, b, hu0, hu1, hb, hbu, rfl⟩ k hk
    have e : (u * b).submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) =
        u.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) *
          b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      symm
      refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
      intro m hm
      have hkm : k ≤ m.val := by
        by_contra hlt
        exact hm ⟨⟨m.val, not_le.1 hlt⟩, rfl⟩
      have : Fin.castLE hk j < m := by
        rw [Fin.lt_def]; exact lt_of_lt_of_le j.2 hkm
      have h0 : b m (Fin.castLE hk j) = 0 := hb this
      rw [h0, mul_zero]
    rw [e, Matrix.det_mul, det_eq_one_of_lower_unitriangular, one_mul]
    · exact isUnit_det_of_upper_of_isUnit_diag _ (fun i j hij => hb hij) (fun i => hbu _)
    · intro i j hij; exact hu0 _ _ hij
    · intro i; exact hu1 _
  · rintro u u' b b' ⟨hu0, hu1⟩ ⟨hu0', hu1'⟩ hb hb' hbu h
    have hd := isUnit_det_of_upper_of_isUnit_diag b hb hbu
    have hu : u = u' * (b' * b⁻¹) := by
      rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hbi : b⁻¹.BlockTriangular id := by
      let _ := Matrix.invertibleOfIsUnitDet b hd
      exact Matrix.blockTriangular_inv_of_blockTriangular hb
    have hc : b' * b⁻¹ = 1 := by
      refine eq_one_of_lower_unitriangular_eq_mul (u.submatrix ι id) (u'.submatrix ι id) _
        hu0 hu1 hu0' hu1' (hb'.mul hbi) ?_
      ext i j
      rw [Matrix.submatrix_apply, hu]; simp [Matrix.mul_apply]
    refine ⟨by rw [hu, hc, Matrix.mul_one], ?_⟩
    calc b = b' * b⁻¹ * b := by rw [hc, Matrix.one_mul]
      _ = b' := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

end GlobalTheory
