import ReciprocityTheory.AnalyticForms.LeviForms.HomDensA

namespace ReciprocityTheory.AnForm.P

open Polynomial Matrix

noncomputable section

theorem cf_mul_zero {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 0 (P * Q) = cf 0 P * cf 0 Q := by
  rw [cf_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem cf_mul_one {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 1 (P * Q) = cf 0 P * cf 1 Q + cf 1 P * cf 0 Q := by
  rw [cf_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem cf_mul_two {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 2 (P * Q) = cf 0 P * cf 2 Q + cf 1 P * cf 1 Q + cf 2 P * cf 0 Q := by
  rw [cf_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

def zMat (N : ℕ) (z : Pairs N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ p : Pairs N, Matrix.single p.1.2 p.1.1 (z p)

theorem cellMat_eq (N : ℕ) (z : Pairs N → ℂ) :
    cellMat N z = ∑ k ∈ Finset.range N, ((k.factorial : ℂ)⁻¹) • zMat N z ^ k := rfl

theorem zMat_apply (N : ℕ) (z : Pairs N → ℂ) (i j : Fin N) :
    zMat N z i j = if h : j < i then z ⟨(j, i), h⟩ else 0 := by
  simp only [zMat, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(j, i), h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h2 h1))
    · simp
  · refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (by rw [← h1, ← h2]; exact p.2)

theorem zMat_eq_zero_of_le {N : ℕ} (z : Pairs N → ℂ) {i j : Fin N} (h : i ≤ j) :
    zMat N z i j = 0 := by
  rw [zMat_apply, dif_neg (not_lt.2 h)]

theorem zMat_mul_swap (N : ℕ) (z : Pairs N → ℂ) (i j : Fin N) :
    zMat N z i j * zMat N z j i = 0 := by
  rcases le_total i j with h | h
  · rw [zMat_eq_zero_of_le z h, zero_mul]
  · rw [zMat_eq_zero_of_le z h, mul_zero]

theorem zMat_smul (N : ℕ) (z : Pairs N → ℂ) (c : ℂ) : zMat N (c • z) = c • zMat N z := by
  ext i j
  rw [zMat_apply, Matrix.smul_apply, zMat_apply]
  split_ifs <;> simp

theorem zMat_real_smul (N : ℕ) (z : Pairs N → ℂ) (s : ℝ) :
    zMat N (s • z) = (s : ℂ) • zMat N z := by
  rw [← zMat_smul]
  congr 1

theorem zMat_of_le_one {N : ℕ} (z : Pairs N → ℂ) (hN : N ≤ 1) : zMat N z = 0 := by
  ext i j
  rw [zMat_apply, dif_neg]
  · rfl
  intro h
  have := Fin.lt_iff_val_lt_val.1 h
  have := i.isLt
  omega

theorem zsq_diag (N : ℕ) (z : Pairs N → ℂ) (i : Fin N) : (zMat N z ^ 2) i i = 0 := by
  rw [pow_two, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => zMat_mul_swap N z i k

theorem zhsq_diag (N : ℕ) (z : Pairs N → ℂ) (i : Fin N) : ((zMat N z)ᴴ ^ 2) i i = 0 := by
  rw [← conjTranspose_pow, conjTranspose_apply, zsq_diag, star_zero]

theorem coeff_X_pow_mul_C (a : ℂ) (k n : ℕ) : (X ^ k * C a).coeff n = if n = k then a else 0 := by
  rw [mul_comm, coeff_C_mul_X_pow]

def cpP (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ[X] :=
  ∑ k ∈ Finset.range N, (X ^ k : ℂ[X]) • ((((k.factorial : ℂ)⁻¹) • A ^ k).map C)

theorem cf_cpP (N n : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    cf n (cpP N A) = if n < N then ((n.factorial : ℂ)⁻¹) • A ^ n else 0 := by
  ext i j
  simp only [cpP, cf_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    finsetSum_coeff, coeff_X_pow_mul_C]
  rw [Finset.sum_ite_eq]
  by_cases h : n < N <;> simp [h]

theorem coeffMatrix_zero_truncExpPoly (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : cf 0 (cpP N A) = 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Subsingleton.elim _ _
  · rw [cf_cpP, if_pos hN]; simp

theorem coeffMatrix_one_truncExpPoly (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (hA : N ≤ 1 → A = 0) :
    cf 1 (cpP N A) = A := by
  rw [cf_cpP]
  split_ifs with h
  · simp
  · exact (hA (by omega)).symm

theorem coeffMatrix_two_truncExpPoly (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ∃ c : ℂ, cf 2 (cpP N A) = c • A ^ 2 := by
  rw [cf_cpP]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩

def gP (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) : Matrix (Fin N) (Fin N) ℂ[X] :=
  cpP N (zMat N v)ᴴ * ((diagonal fun k => (hd k : ℂ)).map C * cpP N (zMat N v))

theorem coeffMatrix_zero_gramPoly (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) :
    cf 0 (gP N hd v) = diagonal fun k => (hd k : ℂ) := by
  rw [gP, cf_mul_zero, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, Matrix.one_mul, Matrix.mul_one]

theorem coeffMatrix_one_gramPoly (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) :
    cf 1 (gP N hd v) = (diagonal fun k => (hd k : ℂ)) * zMat N v +
      (zMat N v)ᴴ * diagonal fun k => (hd k : ℂ) := by
  have h1 := coeffMatrix_one_truncExpPoly N (zMat N v) (fun h => zMat_of_le_one v h)
  have h2 := coeffMatrix_one_truncExpPoly N (zMat N v)ᴴ (fun h => by rw [zMat_of_le_one v h, conjTranspose_zero])
  rw [gP, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, h1, h2, Matrix.one_mul,
    Matrix.mul_one]

theorem coeffMatrix_two_gramPoly_diag (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) (i : Fin N) :
    cf 2 (gP N hd v) i i = ∑ k, star (zMat N v k i) * ((hd k : ℂ) * zMat N v k i) := by
  have h1 := coeffMatrix_one_truncExpPoly N (zMat N v) (fun h => zMat_of_le_one v h)
  have h2 := coeffMatrix_one_truncExpPoly N (zMat N v)ᴴ (fun h => by rw [zMat_of_le_one v h, conjTranspose_zero])
  obtain ⟨c1, e1⟩ := coeffMatrix_two_truncExpPoly N (zMat N v)
  obtain ⟨c2, e2⟩ := coeffMatrix_two_truncExpPoly N (zMat N v)ᴴ
  rw [gP, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, h1, h2, e1, e2]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, zsq_diag, zhsq_diag,
    mul_zero, zero_mul, zero_add, add_zero]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, conjTranspose_apply]

def Zm (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (zMat N v).submatrix (Fin.castLE hm) (Fin.castLE hm)

def Gm (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    Matrix (Fin m) (Fin m) ℂ[X] :=
  (gP N hd v).submatrix (Fin.castLE hm) (Fin.castLE hm)

def tL {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  1 - (X : ℂ[X]) • A.map C

def Gn (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    Matrix (Fin m) (Fin m) ℂ[X] :=
  tL (Zm N m hm v)ᴴ * Gm N hd m hm v * tL (Zm N m hm v)

theorem coeffMatrix_zero_unipotentLine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : cf 0 (tL A) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [tL, cf_apply, h, Matrix.one_apply, coeff_X_mul_C, coeff_one]

theorem coeffMatrix_one_unipotentLine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : cf 1 (tL A) = -A := by
  ext i j
  by_cases h : i = j <;> simp [tL, cf_apply, h, Matrix.one_apply, coeff_X_mul_C, coeff_one]

theorem coeffMatrix_two_unipotentLine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : cf 2 (tL A) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [tL, cf_apply, h, Matrix.one_apply, coeff_X_mul_C, coeff_one]

theorem castLE_le {N m : ℕ} (hm : m ≤ N) {i j : Fin m} (h : i ≤ j) :
    Fin.castLE hm i ≤ Fin.castLE hm j :=
  Fin.le_iff_val_le_val.2 (by simpa using Fin.le_iff_val_le_val.1 h)

theorem det_tL_lower (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) : (tL (Zm N m hm v)).det = 1 := by
  rw [det_of_isLowerTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [tL, Zm, zMat_eq_zero_of_le v le_rfl]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [tL, Zm, Matrix.one_apply, hij'.ne, zMat_eq_zero_of_le v (castLE_le hm hij'.le)]

theorem det_tL_upper (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    (tL (Zm N m hm v)ᴴ).det = 1 := by
  rw [det_of_isUpperTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [tL, Zm, zMat_eq_zero_of_le v le_rfl]
  · intro i j hij
    have hij' : j < i := hij
    simp [tL, Zm, Matrix.one_apply, hij'.ne', zMat_eq_zero_of_le v (castLE_le hm hij'.le)]

theorem det_Gn (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    (Gn N hd m hm v).det = (Gm N hd m hm v).det := by
  rw [Gn, det_mul, det_mul, det_tL_upper, det_tL_lower, one_mul, mul_one]

theorem coeffMatrix_zero_gramPolyMinor (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 0 (Gm N hd m hm v) = diagonal fun a => (hd (Fin.castLE hm a) : ℂ) := by
  show (cf 0 (gP N hd v)).submatrix _ _ = _
  rw [coeffMatrix_zero_gramPoly, submatrix_diagonal _ _ (Fin.castLE_injective hm)]
  rfl

theorem coeffMatrix_one_gramPolyMinor_apply (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ)
    (a b : Fin m) : cf 1 (Gm N hd m hm v) a b =
      (hd (Fin.castLE hm a) : ℂ) * zMat N v (Fin.castLE hm a) (Fin.castLE hm b) +
        star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) * (hd (Fin.castLE hm b) : ℂ) := by
  show cf 1 (gP N hd v) _ _ = _
  rw [coeffMatrix_one_gramPoly]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, conjTranspose_apply]

theorem coeffMatrix_zero_reducedGramPolyMinor (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 0 (Gn N hd m hm v) = diagonal fun a => (hd (Fin.castLE hm a) : ℂ) := by
  rw [Gn, cf_mul_zero, cf_mul_zero, coeffMatrix_zero_unipotentLine, coeffMatrix_zero_unipotentLine, Matrix.one_mul, Matrix.mul_one, coeffMatrix_zero_gramPolyMinor]

theorem coeffMatrix_one_reducedGramPolyMinor (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 1 (Gn N hd m hm v) = 0 := by
  have e : cf 1 (Gn N hd m hm v) = cf 1 (Gm N hd m hm v) - (Zm N m hm v)ᴴ * cf 0 (Gm N hd m hm v) -
      cf 0 (Gm N hd m hm v) * Zm N m hm v := by
    simp only [Gn, cf_mul_zero, cf_mul_one, coeffMatrix_zero_unipotentLine, coeffMatrix_one_unipotentLine]
    noncomm_ring
  rw [e, coeffMatrix_zero_gramPolyMinor]
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, coeffMatrix_one_gramPolyMinor_apply,
    conjTranspose_apply, Zm, submatrix_apply, Matrix.zero_apply]
  ring

theorem conjTranspose_mul_coeffMatrix_one_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    ((Zm N m hm v)ᴴ * cf 1 (Gm N hd m hm v)) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have k := zMat_mul_swap N v (Fin.castLE hm a) (Fin.castLE hm b)
  have k' : star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
      star (zMat N v (Fin.castLE hm a) (Fin.castLE hm b)) = 0 := by
    rw [← star_mul, k, star_zero]
  simp only [conjTranspose_apply, Zm, submatrix_apply, coeffMatrix_one_gramPolyMinor_apply]
  linear_combination (hd (Fin.castLE hm a) : ℂ) * k'

theorem coeffMatrix_one_mul_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    (cf 1 (Gm N hd m hm v) * Zm N m hm v) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have k := zMat_mul_swap N v (Fin.castLE hm a) (Fin.castLE hm b)
  simp only [Zm, submatrix_apply, coeffMatrix_one_gramPolyMinor_apply]
  linear_combination (hd (Fin.castLE hm a) : ℂ) * k

theorem conjTranspose_mul_diagonal_mul_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    ((Zm N m hm v)ᴴ * (diagonal fun a => (hd (Fin.castLE hm a) : ℂ)) * Zm N m hm v) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.mul_diagonal, conjTranspose_apply, Zm, submatrix_apply]
  ring

theorem coeffMatrix_two_reducedGramPolyMinor_apply (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    cf 2 (Gn N hd m hm v) a a =
      ∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  have e : cf 2 (Gn N hd m hm v) = cf 2 (Gm N hd m hm v) -
      (Zm N m hm v)ᴴ * cf 1 (Gm N hd m hm v) - cf 1 (Gm N hd m hm v) * Zm N m hm v +
      (Zm N m hm v)ᴴ * cf 0 (Gm N hd m hm v) * Zm N m hm v := by
    simp only [Gn, cf_mul_zero, cf_mul_one, cf_mul_two, coeffMatrix_zero_unipotentLine, coeffMatrix_one_unipotentLine, coeffMatrix_two_unipotentLine]
    noncomm_ring
  rw [e, coeffMatrix_zero_gramPolyMinor, Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply, conjTranspose_mul_coeffMatrix_one_diag, coeffMatrix_one_mul_diag, conjTranspose_mul_diagonal_mul_diag]
  have h2 : cf 2 (Gm N hd m hm v) a a = cf 2 (gP N hd v) (Fin.castLE hm a) (Fin.castLE hm a) :=
    rfl
  rw [h2, coeffMatrix_two_gramPoly_diag]
  ring

theorem eval_cpP (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    (cpP N A).map (eval t) = ∑ k ∈ Finset.range N, (t ^ k * ((k.factorial : ℂ)⁻¹)) • A ^ k := by
  ext i j
  simp only [cpP, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← coe_evalRingHom, map_sum]
  simp [mul_assoc]

theorem det_gramPolyMinor_coeff_zero_one (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    (Gm N hd m hm v).det.coeff 0 = ((∏ a : Fin m, hd (Fin.castLE hm a) : ℝ) : ℂ) ∧
      (Gm N hd m hm v).det.coeff 1 = 0 := by
  obtain ⟨h0, h1⟩ := det_coeff_zero_one_of_coeffMatrix_one (Gn N hd m hm v) (coeffMatrix_one_reducedGramPolyMinor N hd m hm v)
  rw [det_Gn] at h0 h1
  rw [h0, coeffMatrix_zero_reducedGramPolyMinor, det_diagonal, Complex.ofReal_prod]
  exact ⟨rfl, h1⟩

theorem coeff2_Gm (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (v : Pairs N → ℂ) :
    (Gm N hd m hm v).det.coeff 2 = (∏ a : Fin m, (hd (Fin.castLE hm a) : ℂ)) *
      ∑ a : Fin m, ((hd (Fin.castLE hm a) : ℂ))⁻¹ *
        (∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
        ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
          ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a))) := by
  rw [← det_Gn, coeff2_det_of (Gn N hd m hm v) (fun a => (hd (Fin.castLE hm a) : ℂ))
    (fun a => by exact_mod_cast hd0 _) (coeffMatrix_zero_reducedGramPolyMinor N hd m hm v) (coeffMatrix_one_reducedGramPolyMinor N hd m hm v)]
  simp only [coeffMatrix_two_reducedGramPolyMinor_apply]

end

end ReciprocityTheory.AnForm.P
