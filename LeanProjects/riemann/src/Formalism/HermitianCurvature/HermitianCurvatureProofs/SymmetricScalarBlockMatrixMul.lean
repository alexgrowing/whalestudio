import Formalism.HermitianCurvature.StatementU
import Formalism.FormalDegreeBessel.FinalG

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux3

variable {k j ρ : ℕ}

theorem block3_mul
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 (k := k) (j := j) (ρ := ρ) A11 A12 A13 A21 A22 A23 A31 A32 A33 * blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 * ToralGalois + A12 * B21 + A13 * B31) (A11 * cocyclesToWachVectorsExponent + A12 * B22 + A13 * B32) (A11 * B13 + A12 * B23 + A13 * B33)
        (A21 * ToralGalois + A22 * B21 + A23 * B31) (A21 * cocyclesToWachVectorsExponent + A22 * B22 + A23 * B32) (A21 * B13 + A22 * B23 + A23 * B33)
        (A31 * ToralGalois + A32 * B21 + A33 * B31) (A31 * cocyclesToWachVectorsExponent + A32 * B22 + A33 * B32) (A31 * B13 + A32 * B23 + A33 * B33) := by
  simp only [blk3, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  ext ((a | a) | a) ((b | b) | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem block3_one : blk3 (k := k) (j := j) (ρ := ρ) 1 0 0 0 1 0 0 0 1 = 1 := by
  unfold blk3
  have h1 : Matrix.fromRows (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = 0 := by
    ext (a | a) b <;> rfl
  have h2 : Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) = 0 := by
    ext a (b | b) <;> rfl
  rw [h1, h2, Matrix.fromBlocks_one, Matrix.fromBlocks_one]
  simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem block3_apply (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (x y : Ix k j ρ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33 x y := by
  simp [blk3, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem block_index_first_val (a : Fin j) : (eB k j ρ (Sum.inl (Sum.inl a))).val = a.val := by
  simp [eB]
theorem block_index_middle_val (i : Fin (2 * ρ + k + 1)) : (eB k j ρ (Sum.inl (Sum.inr i))).val = j + i.val := by
  simp [eB]
theorem block_index_last_val (a : Fin j) : (eB k j ρ (Sum.inr a)).val = j + (2 * ρ + k + 1) + a.val := by
  simp [eB]

theorem wMat_mul_apply {n : ℕ} {m : Type*} (A : Matrix (Fin n) m ℂ) (a : Fin n) (b : m) :
    (G.wMat n * A) a b = A a.rev b := by
  simp [G.wMat, Matrix.mul_apply, ite_mul]

theorem wMat_mul_self (n : ℕ) : G.wMat n * G.wMat n = 1 := by
  ext a b
  rw [wMat_mul_apply]
  by_cases h : a = b
  · subst h
    simp [G.wMat]
  · simp [G.wMat, Matrix.one_apply, h, Ne.symm h]

theorem hat_z_of_block3 (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    Zh k j ρ (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = G.wMat j * A31 := by
  ext a b
  rw [wMat_mul_apply]
  have h1 : (⟨2 * (j + ρ) + k - a.val, by omega⟩ : Fin (2 * (j + ρ) + k + 1)) = eB k j ρ (Sum.inr a.rev) := by
    apply Fin.ext
    rw [block_index_last_val]
    simp only [Fin.val_rev]
    omega
  have h2 : (⟨b.val, by omega⟩ : Fin (2 * (j + ρ) + k + 1)) = eB k j ρ (Sum.inl (Sum.inl b)) := by
    apply Fin.ext
    rw [block_index_first_val]
  simp only [Zh]
  rw [h1, h2, block3_apply]
  simp

theorem uni_mul_inv (a : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin j) (Fin j) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    blk3 1 a b 0 1 c 0 0 1 * blk3 1 (-a) (a * c - b) 0 1 (-c) 0 0 1 = 1 := by
  rw [block3_mul, ← block3_one]
  congr 1 <;> simp <;> abel

theorem uni_inv (a : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin j) (Fin j) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    (blk3 1 a b 0 1 c 0 0 1)⁻¹ = blk3 1 (-a) (a * c - b) 0 1 (-c) 0 0 1 := Matrix.inv_eq_right_inv (uni_mul_inv a b c)

theorem rn_eq (x : RC k j ρ) : Rn k j ρ x = blk3 1 (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ))
    (G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2))
    0 1 (Matrix.of x.1) 0 0 1 := rfl

theorem zhSlice : ZhSlice := by
  intro k j ρ x x' Z γ
  rw [rn_eq, rn_eq, uni_inv]
  simp only [mMap]
  rw [block3_mul, block3_mul, hat_z_of_block3]
  simp [← Matrix.mul_assoc, wMat_mul_self]

theorem hpk_row (k r : ℕ) (a : ℕ) (ha : a < r) (c : Fin (2 * r + k + 1)) :
    Hpk k r ⟨a, by omega⟩ c = if c = ⟨2 * r + k - a, by omega⟩ then 1 else 0 := by
  unfold Hpk
  by_cases hc : c = ⟨2 * r + k - a, by omega⟩
  · rw [if_pos hc, if_pos]
    subst hc
    refine ⟨ha, ?_⟩
    show a + (2 * r + k - a) = 2 * r + k
    omega
  · rw [if_neg hc]
    have hv : c.val ≠ 2 * r + k - a := fun h => hc (Fin.ext h)
    have e1 : ¬ ((⟨a, by omega⟩ : Fin (2 * r + k + 1)).val < r ∧ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val + c.val = 2 * r + k) := by
      rintro ⟨_, h⟩; exact hv (by simp only at h; omega)
    have e2 : ¬ (c.val < r ∧ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val + c.val = 2 * r + k) := by
      rintro ⟨_, h⟩; exact hv (by simp only at h; omega)
    have e3 : ¬ (r ≤ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val ∧ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val ≤ r + k ∧
        (⟨a, by omega⟩ : Fin (2 * r + k + 1)) = c) := by
      rintro ⟨h, _⟩; simp only at h; omega
    rw [if_neg e1, if_neg e2, if_neg e3]

theorem zhat_apply_low (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a b : Fin (r + 1)) (ha : a.val < r) (hb : b.val < r) :
    Zhat k r z z' g a b = g ⟨2 * r + k - a.val, by omega⟩ ⟨b.val, by omega⟩ := by
  unfold Zhat fvec herm
  rw [dif_pos ha, dif_pos hb]
  have hstar : star (bvec (eI k r ⟨a.val, ha⟩)) = bvec (eI k r ⟨a.val, ha⟩) := by
    ext i; simp only [bvec, Pi.star_apply, Pi.single_apply]; split_ifs <;> simp
  rw [hstar]
  simp only [bvec, eI]
  rw [Matrix.mulVec_single, single_dotProduct, one_mul, Matrix.mulVec, dotProduct]
  simp_rw [hpk_row k r a.val ha]
  simp

theorem zhDmin : ZhDmin := by
  intro k j ρ z z' g
  unfold Dmin DjU
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  rw [zhat_apply_low]
  · rfl
  · simp; omega
  · simp; omega

theorem symmetricScalarBlockMatrix_mul {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' = blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [blk2, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block2_det_lower_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A 0 C D).det = A.det * D.det := by
  simp only [blk2]
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

theorem block2_det_upper_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A B 0 D).det = A.det * D.det := by
  simp only [blk2]
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem det_upper {p : ℕ} (u : G.UT p → ℂ) : (G.upper u).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [G.upper, G.strictUpper]
  · intro a b hab
    have hab' : b < a := hab
    have hne : a ≠ b := (ne_of_lt hab').symm
    have hnl : ¬ a < b := not_lt.mpr hab'.le
    simp [G.upper, G.strictUpper, Matrix.one_apply, hne, hnl]

theorem det_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) : (lowW σ v).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [lowW]
  · intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    simp [lowW, Matrix.one_apply, ne_of_lt hab', not_lt.mpr hab'.le]

theorem detZj : DetZj := by
  intro p s σ d η Z
  unfold ZjH Zj headH hMat G.detM
  rw [Matrix.det_mul, Matrix.det_mul, block2_det_lower_triangular, block2_det_lower_triangular, block2_det_upper_triangular]
  simp only [Matrix.det_mul, det_upper, det_lowW, Matrix.det_one]
  ring

theorem block3_conjTranspose (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33)ᴴ =
      blk3 A11ᴴ A21ᴴ A31ᴴ A12ᴴ A22ᴴ A32ᴴ A13ᴴ A23ᴴ A33ᴴ := by
  unfold blk3
  rw [Matrix.conjTranspose_reindex]
  congr 1
  ext ((a | a) | a) ((b | b) | b) <;> simp

theorem hpkBlocks : HpkBlocks := by
  intro k j ρ
  ext i l
  rcases h : (eB k j ρ).symm i with ((a | a) | a) <;> rcases h' : (eB k j ρ).symm l with ((b | b) | b) <;>
    (rw [← (eB k j ρ).apply_symm_apply i, ← (eB k j ρ).apply_symm_apply l, h, h']) <;>
    (rw [block3_apply]; simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply, G.wMat, Matrix.of_apply]
     unfold Hpk
     simp only [Fin.ext_iff, block_index_first_val, block_index_middle_val, block_index_last_val, Fin.val_rev]
     split_ifs <;> first | rfl | (exfalso; omega))

theorem wMat_conjTranspose (n : ℕ) : (G.wMat n)ᴴ = G.wMat n := by
  ext a b
  simp only [Matrix.conjTranspose_apply, G.wMat, Matrix.of_apply]
  have h : (a = b.rev) ↔ (b = a.rev) := by
    constructor <;> rintro rfl <;> simp
  simp only [h]
  split_ifs <;> simp

theorem skewOf_conjTranspose {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  ext a b
  simp only [skewOf, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    star_add, star_sub, star_star, Matrix.diagonal_apply]
  by_cases h : b = a
  · subst h
    simp [Complex.conj_ofReal]
    try ring
  · simp [h, Ne.symm h]
    try ring

theorem hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
theorem hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1

theorem mul_wMat_wMat {m : Type*} (n : ℕ) (M : Matrix m (Fin n) ℂ) : M * G.wMat n * G.wMat n = M := by
  rw [Matrix.mul_assoc, wMat_mul_self, Matrix.mul_one]

theorem rn_unitary (x : RC k j ρ) : (Rn k j ρ x)ᴴ * Hpk k (j + ρ) * Rn k j ρ x = Hpk k (j + ρ) := by
  rw [rn_eq, hpkBlocks, block3_conjTranspose, block3_mul, block3_mul]
  congr 1 <;> simp [wMat_conjTranspose, hpk_herm, skewOf_conjTranspose, ← Matrix.mul_assoc, wMat_mul_self, mul_wMat_wMat] <;>
    (ext a b; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply]; ring)

theorem uni_nset (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (hU : (blk3 1 A12 A13 0 1 A23 0 0 1)ᴴ * Hpk k (j + ρ) * blk3 1 A12 A13 0 1 A23 0 0 1 = Hpk k (j + ρ)) :
    blk3 1 A12 A13 0 1 A23 0 0 1 ∈ Nset k (j + ρ) := by
  refine ⟨hU, ?_, ?_⟩
  · intro a i hai
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, hy⟩ := (eB k j ρ).surjective (eI k (j + ρ) a)
    rw [← hy, block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    have hv := congrArg Fin.val hy
    have ha := a.isLt
    simp only [eI] at hv
    rw [← hv] at hai
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [block_index_first_val, block_index_middle_val, block_index_last_val] at hv hai <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)
  · intro i c hc1 hc2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective c
    rw [block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [block_index_first_val, block_index_middle_val, block_index_last_val] at hc1 hc2 hi <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)

theorem rn_nset (x : RC k j ρ) : Rn k j ρ x ∈ Nset k (j + ρ) := by
  have h := rn_unitary x
  rw [rn_eq] at h ⊢
  exact uni_nset _ _ _ h

theorem nset_sset {r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : m ∈ Nset k r) : m ∈ Sset k r z := by
  refine ⟨1, ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩, m, hm, by simp⟩
  · simp [UH]
  · simp
  · simp
  · simp

def eC (j ρ : ℕ) : Fin j ⊕ Fin (ρ + 1) ≃ Fin (j + ρ + 1) := finSumFinEquiv.trans (finCongr (by omega))

theorem column_index_first_val (a : Fin j) : (eC j ρ (Sum.inl a)).val = a.val := by
  simp [eC]
theorem column_index_second_val (c : Fin (ρ + 1)) : (eC j ρ (Sum.inr c)).val = j + c.val := by
  simp [eC]

def F0 (Fj : Matrix (Fin (2 * ρ + k + 1)) (Fin (ρ + 1)) ℂ) : Matrix (Ix k j ρ) (Fin j ⊕ Fin (ρ + 1)) ℂ :=
  Matrix.fromRows (Matrix.fromBlocks 1 0 0 Fj) 0

theorem fm_eq (z : Fin (2 * (j + ρ) + k + 1) → ℂ) (hz : inWb k (j + ρ) z) :
    Formalism.QuantumDeterminants.Fm k (j + ρ) z = Matrix.reindex (eB k j ρ) (eC j ρ) (F0 (Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z))) := by
  ext i c
  obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨y, rfl⟩ := (eC j ρ).surjective c
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply, F0]
  rcases x with ((x | x) | x) <;> rcases y with (y | y)
  · rw [fvec_apply_lt z hz _ _ (by rw [block_index_first_val]; omega), block_index_first_val, column_index_first_val]
    simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  · rw [fvec_apply_lt z hz _ _ (by rw [block_index_first_val]; omega), block_index_first_val, column_index_second_val, if_neg (by omega)]
    simp
  · by_cases hlt : j + x.val < j + ρ
    · rw [fvec_apply_lt z hz _ _ (by rw [block_index_middle_val]; omega), block_index_middle_val, column_index_first_val, if_neg (by omega)]
      simp
    · rw [fvec_apply_ge z _ _ (by rw [block_index_middle_val]; omega), column_index_first_val, if_neg (by omega)]
      simp
  · simp only [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    unfold fvec
    rw [column_index_second_val]
    by_cases hc : y.val < ρ
    · rw [dif_pos (by omega), dif_pos hc]
      simp only [bvec, eI, Pi.single_apply, Fin.ext_iff, block_index_middle_val]
      by_cases hxy : x.val = y.val
      · rw [if_pos (by omega), if_pos hxy]
      · rw [if_neg (by omega), if_neg hxy]
    · rw [dif_neg (by omega), dif_neg hc]
      simp only [lowV]
      congr 1
  · rw [fvec_apply_ge z _ _ (by rw [block_index_last_val]; omega), hz _ (Or.inr (by rw [block_index_last_val]; omega))]
    simp
  · rw [fvec_apply_ge z _ _ (by rw [block_index_last_val]; omega), hz _ (Or.inr (by rw [block_index_last_val]; omega))]
    simp

theorem fq_of_block3 (Fj Fj' : Matrix (Fin (2 * ρ + k + 1)) (Fin (ρ + 1)) ℂ)
    (Q11 : Matrix (Fin j) (Fin j) ℂ) (Q12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (ColumnFamilies : Matrix (Fin j) (Fin j) ℂ)
    (Q21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (Q22 : B.Mat k ρ) (Q23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (Q31 : Matrix (Fin j) (Fin j) ℂ) (Q32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (Q33 : Matrix (Fin j) (Fin j) ℂ) :
    (Matrix.reindex (eB k j ρ) (eC j ρ) (F0 Fj))ᴴ * blk3 Q11 Q12 ColumnFamilies Q21 Q22 Q23 Q31 Q32 Q33 *
        Matrix.reindex (eB k j ρ) (eC j ρ) (F0 Fj') =
      Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Q11 (Q12 * Fj') (Fjᴴ * Q21) (Fjᴴ * Q22 * Fj')) := by
  unfold blk3
  rw [Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  ext (a | a) (b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, F0, Matrix.conjTranspose_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.one_apply]

theorem z_hat_of_block3 (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (hz : inWb k (j + ρ) z) (hz' : inWb k (j + ρ) z')
    (product_first_partition : Matrix (Fin j) (Fin j) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin j) (Fin j) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (BlochKatoReduction : Matrix (Fin j) (Fin j) ℂ) (SumRepresentations : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin j) (Fin j) ℂ) :
    Zhat k (j + ρ) z z' (blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks (G.wMat j * BlochKatoReduction)
        (G.wMat j * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z'))
        ((Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z'))) := by
  rw [Formalism.QuantumDeterminants.Zhat_eq, Matrix.mul_assoc ((Formalism.QuantumDeterminants.Fm k (j + ρ) z)ᴴ), hpkBlocks, block3_mul, fm_eq z hz, fm_eq z' hz',
    fq_of_block3]
  congr 1
  simp

theorem eC_symm_castAdd {l : ℕ} (h : j + l ≤ j + ρ + 1) (a : Fin j) :
    (eC j ρ).symm (Fin.castLE h (Fin.castAdd l a)) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [column_index_first_val]

theorem eC_symm_natAdd {l : ℕ} (h : j + l ≤ j + ρ + 1) (hl : l ≤ ρ + 1) (c : Fin l) :
    (eC j ρ).symm (Fin.castLE h (Fin.natAdd j c)) = Sum.inr (Fin.castLE hl c) := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [column_index_second_val]

theorem minor_blocks (Z : Matrix (Fin j) (Fin j) ℂ) (W : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ) (l : ℕ)
    (hl : l ≤ ρ + 1) (h : j + l ≤ j + ρ + 1) :
    ((Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Z 0 0 W)).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      Z.det * (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : (Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Z 0 0 W)).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks Z 0 0 (W.submatrix (Fin.castLE hl) (Fin.castLE hl))) := by
    ext a b
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
      simp [Matrix.reindex_apply, eC_symm_castAdd h, eC_symm_natAdd h hl]
  rw [e, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem herm_eq_zhat (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v v = Zhat k r v v 1 (Fin.last r) (Fin.last r) := by
  simp [Zhat, fvec]

theorem tz_low (v : Fin (2 * (j + ρ) + k + 1) → ℂ) (hv : inWb k (j + ρ) v) :
    Tz k (j + ρ) v = Tz k ρ (lowV k j ρ v) := by
  unfold Tz
  rw [herm_eq_zhat, herm_eq_zhat,
    show (1 : Matrix (Fin (2 * (j + ρ) + k + 1)) (Fin (2 * (j + ρ) + k + 1)) ℂ) = blk3 1 0 0 0 1 0 0 0 1 from
      block3_one.symm, z_hat_of_block3 v v hv hv]
  have hl : (Fin.last (j + ρ)) = eC j ρ (Sum.inr (Fin.last ρ)) := by ext; rw [column_index_second_val]; simp
  rw [hl, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂,
    Formalism.QuantumDeterminants.Zhat_eq, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc]

theorem gfSlice : GfSlice := by
  intro k j ρ z z' hz hz' x x' Z γ
  have hs : (Rn k j ρ x)⁻¹ ∈ Sset k (j + ρ) z := nset_sset z ((Formalism.QuantumDeterminants.nSubgroup k (j + ρ)).2.2 _ (rn_nset x))
  have hs' : Rn k j ρ x' ∈ Sset k (j + ρ) z' := nset_sset z' (rn_nset x')
  rw [Formalism.QuantumDeterminants.gInv k (j + ρ) z z' hz hz' _ hs _ hs' (mMap k j ρ Z γ)]
  have hZ : Zhat k (j + ρ) z z' (mMap k j ρ Z γ) =
      Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ (lowV k j ρ z) (lowV k j ρ z') γ)) := by
    unfold mMap
    rw [z_hat_of_block3 z z' hz hz', Formalism.QuantumDeterminants.Zhat_eq]
    congr 1
    simp [← Matrix.mul_assoc, wMat_mul_self]
  have h1 : Dmin k (j + ρ) z z' (mMap k j ρ Z γ) (Fin.last _) =
      Z.det * Dmin k ρ (lowV k j ρ z) (lowV k j ρ z') γ (Fin.last _) := by
    unfold Dmin
    rw [hZ]
    exact minor_blocks _ _ (ρ + 1) le_rfl _
  have h0 : Dmin k (j + ρ) z z' (mMap k j ρ Z γ) ⟨j + ρ, by omega⟩ =
      Z.det * Dmin k ρ (lowV k j ρ z) (lowV k j ρ z') γ ⟨ρ, by omega⟩ := by
    unfold Dmin
    rw [hZ]
    exact minor_blocks _ _ ρ (by omega) _
  unfold Gf
  rw [h1, h0, tz_low z hz, tz_low z' hz', Complex.normSq_mul, Complex.normSq_mul]
  ring

theorem block3_eq_iff
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 (k := k) (j := j) (ρ := ρ) A11 A12 A13 A21 A22 A23 A31 A32 A33 = blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 ↔
      A11 = ToralGalois ∧ A12 = cocyclesToWachVectorsExponent ∧ A13 = B13 ∧ A21 = B21 ∧ A22 = B22 ∧ A23 = B23 ∧ A31 = B31 ∧ A32 = B32 ∧ A33 = B33 := by
  constructor
  · intro h
    have e : ∀ x y : Ix k j ρ, Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23)
        (Matrix.fromCols A31 A32) A33 x y = Matrix.fromBlocks (Matrix.fromBlocks ToralGalois cocyclesToWachVectorsExponent B21 B22) (Matrix.fromRows B13 B23)
        (Matrix.fromCols B31 B32) B33 x y := by
      intro x y
      rw [← block3_apply, ← block3_apply, h]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b
    · simpa using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b))
    · simpa using e (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inr b))
    · simpa [Matrix.fromRows_apply_inl] using e (Sum.inl (Sum.inl a)) (Sum.inr b)
    · simpa using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inl b))
    · simpa using e (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inr b))
    · simpa [Matrix.fromRows_apply_inr] using e (Sum.inl (Sum.inr a)) (Sum.inr b)
    · simpa [Matrix.fromCols_apply_inl] using e (Sum.inr a) (Sum.inl (Sum.inl b))
    · simpa [Matrix.fromCols_apply_inr] using e (Sum.inr a) (Sum.inl (Sum.inr b))
    · simpa using e (Sum.inr a) (Sum.inr b)
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem rn_mul_inv (x : RC k j ρ) : Rn k j ρ x * (Rn k j ρ x)⁻¹ = 1 := by
  rw [rn_eq, uni_inv, uni_mul_inv]

theorem uni_inv_mul (a : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (b : Matrix (Fin j) (Fin j) ℂ)
    (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) :
    blk3 1 (-a) (a * c - b) 0 1 (-c) 0 0 1 * blk3 1 a b 0 1 c 0 0 1 = 1 := by
  rw [block3_mul, ← block3_one]
  congr 1 <;> simp <;> abel

theorem rn_inv_mul (x : RC k j ρ) : (Rn k j ρ x)⁻¹ * Rn k j ρ x = 1 := by
  rw [rn_eq, uni_inv, uni_inv_mul]

theorem cancel_right {m : Type*} {n : ℕ} (X : Matrix m (Fin n) ℂ) (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det)
    (h : X * W = 0) : X = 0 := by
  calc X = X * W * W⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hW, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem cancel_left {m : Type*} {n : ℕ} (X : Matrix (Fin n) m ℂ) (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det)
    (h : W * X = 0) : X = 0 := by
  calc X = W⁻¹ * (W * X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hW, Matrix.one_mul]
    _ = 0 := by rw [h, Matrix.mul_zero]

theorem isUnit_of_mul_self {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (h : W * W = 1) : IsUnit W.det := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact ⟨⟨W.det, W.det, h2, h2⟩, rfl⟩

theorem wMat_det (n : ℕ) : IsUnit (G.wMat n).det := isUnit_of_mul_self _ (wMat_mul_self n)

theorem gv_det {r : ℕ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) : IsUnit γ.det := by
  have h : γᴴ * Hpk k r * γ = Hpk k r := hγ
  have hH : IsUnit (Hpk k r).det := isUnit_of_mul_self _ (hpk_sq k r)
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : IsUnit ((γᴴ).det * (Hpk k r).det * γ.det) := by
    rw [h2]
    exact hH
  exact isUnit_of_mul_isUnit_right h3

theorem skewOf_apply_lt {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a b : Fin n) (h : a < b) :
    skewOf q a b = q.1 ⟨(a, b), h⟩ := by
  simp [skewOf, G.strictUpper, h, not_lt.mpr h.le, ne_of_lt h]

theorem skewOf_apply_diag {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a : Fin n) :
    skewOf q a a = Complex.I * (q.2 a : ℂ) := by
  simp [skewOf, G.strictUpper]

theorem skewOf_inj {n : ℕ} (q q' : (G.UT n → ℂ) × (Fin n → ℝ)) (h : skewOf q = skewOf q') : q = q' := by
  obtain ⟨u, d⟩ := q
  obtain ⟨u', d'⟩ := q'
  have h1 : u = u' := by
    funext p
    obtain ⟨⟨a, b⟩, hab⟩ := p
    have := congrFun (congrFun h a) b
    simpa only [skewOf_apply_lt _ _ _ hab] using this
  have h2 : d = d' := by
    funext i
    have := congrFun (congrFun h i) i
    simp only [skewOf_apply_diag] at this
    have h3 := mul_left_cancel₀ Complex.I_ne_zero this
    simpa using h3
  rw [h1, h2]

theorem bigCell_uniq (x1 x1' x2 x2' : RC k j ρ) (Z1 Z2 : Matrix (Fin j) (Fin j) ℂ) (γ1 γ2 : B.Mat k ρ)
    (hZ1 : Z1.det ≠ 0) (hZ2 : Z2.det ≠ 0) (hγ2 : γ2 ∈ B.GV k ρ)
    (h : (Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1 * Rn k j ρ x1' = (Rn k j ρ x2)⁻¹ * mMap k j ρ Z2 γ2 * Rn k j ρ x2') :
    x1 = x2 ∧ x1' = x2' ∧ Z1 = Z2 ∧ γ1 = γ2 := by
  have key : Rn k j ρ x2 * (Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1 =
      mMap k j ρ Z2 γ2 * (Rn k j ρ x2' * (Rn k j ρ x1')⁻¹) := by
    calc Rn k j ρ x2 * (Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1
        = Rn k j ρ x2 * ((Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1 * Rn k j ρ x1') * (Rn k j ρ x1')⁻¹ := by
          simp only [Matrix.mul_assoc, rn_mul_inv, Matrix.mul_one]
      _ = Rn k j ρ x2 * ((Rn k j ρ x2)⁻¹ * mMap k j ρ Z2 γ2 * Rn k j ρ x2') * (Rn k j ρ x1')⁻¹ := by rw [h]
      _ = mMap k j ρ Z2 γ2 * (Rn k j ρ x2' * (Rn k j ρ x1')⁻¹) := by
          simp only [← Matrix.mul_assoc, rn_mul_inv, Matrix.one_mul]
  rw [rn_eq x2, rn_eq x1, uni_inv, rn_eq x2', rn_eq x1', uni_inv] at key
  unfold mMap at key
  rw [block3_mul, block3_mul, block3_mul, block3_mul, block3_eq_iff] at key
  obtain ⟨e11, -, -, e21, e22, e23, e31, -, e33⟩ := key
  simp at e11 e21 e22 e23 e31 e33
  have hW1 : IsUnit (G.wMat j * Z1).det := by
    rw [Matrix.det_mul]; exact (wMat_det j).mul (isUnit_iff_ne_zero.mpr hZ1)
  have hW2 : IsUnit (G.wMat j * Z2).det := by
    rw [Matrix.det_mul]; exact (wMat_det j).mul (isUnit_iff_ne_zero.mpr hZ2)
  have hZ : Z1 = Z2 := by
    have := congrArg (G.wMat j * ·) e31
    simpa [← Matrix.mul_assoc, wMat_mul_self] using this
  have hc : x1.1 = x2.1 := by
    have h0 := cancel_right _ _ hW1 e21
    have : -x1.1 + x2.1 = 0 := by
      ext i b; have := congrFun (congrFun h0 i) b; simpa using this
    rw [neg_add_eq_zero] at this; exact this
  have hc' : x1'.1 = x2'.1 := by
    have h0 := cancel_left _ _ (gv_det hγ2) e23.symm
    have : -x1'.1 + x2'.1 = 0 := by
      ext i b; have := congrFun (congrFun h0 i) b; simpa using this
    rw [neg_add_eq_zero] at this; exact this
  have hneg : ∀ y : Fin (2 * ρ + k + 1) → Fin j → ℂ, (Matrix.of (-y) : Matrix _ _ ℂ) = -Matrix.of y := fun y => rfl
  have hS : x1.2 = x2.2 := by
    have h0 := cancel_right _ _ hW1 e11
    rw [← hc, hneg] at h0
    have h1 : G.wMat j * (skewOf x2.2 - skewOf x1.2) = 0 := by
      rw [← h0]
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul]
      abel
    have h2 := cancel_left _ _ (wMat_det j) h1
    exact (skewOf_inj _ _ (sub_eq_zero.mp h2)).symm
  have hS' : x1'.2 = x2'.2 := by
    have h0 := cancel_left _ _ hW2 e33.symm
    rw [← hc', hneg] at h0
    have h1 : G.wMat j * (skewOf x2'.2 - skewOf x1'.2) = 0 := by
      rw [← h0]
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul]
      abel
    have h2 := cancel_left _ _ (wMat_det j) h1
    exact (skewOf_inj _ _ (sub_eq_zero.mp h2)).symm
  exact ⟨Prod.ext hc hS, Prod.ext hc' hS', hZ, e22⟩

theorem block3_eta (M : B.Mat k (j + ρ)) : M = blk3
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inl b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inl a))) (fun b => eB k j ρ (Sum.inr b)))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inl (Sum.inl b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inl (Sum.inr a))) (fun b => eB k j ρ (Sum.inr b)))
    (M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inl (Sum.inl b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inl (Sum.inr b))))
    (M.submatrix (fun a => eB k j ρ (Sum.inr a)) (fun b => eB k j ρ (Sum.inr b))) := by
  ext x y
  obtain ⟨x', rfl⟩ := (eB k j ρ).surjective x
  obtain ⟨y', rfl⟩ := (eB k j ρ).surjective y
  rw [block3_apply]
  rcases x' with ((a | a) | a) <;> rcases y' with ((b | b) | b) <;> simp

theorem hpk_det (k r : ℕ) : IsUnit (Hpk k r).det := isUnit_of_mul_self _ (hpk_sq k r)

theorem unitary_right {r : ℕ} (g : B.Mat k r) (h : gᴴ * Hpk k r * g = Hpk k r) : g * Hpk k r * gᴴ = Hpk k r := by
  have h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, hpk_sq]
  have h2 : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
    rw [← Matrix.inv_eq_left_inv h1]
    exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h1)
  calc g * Hpk k r * gᴴ = g * (Hpk k r * gᴴ * Hpk k r) * Hpk k r := by
        simp only [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
    _ = Hpk k r := by rw [h2, Matrix.one_mul]

def skewCoords {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) : (G.UT n → ℂ) × (Fin n → ℝ) :=
  (fun p => S p.1.1 p.1.2, fun i => (S i i).im)

theorem skewOf_apply_gt {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a b : Fin n) (h : b < a) :
    skewOf q a b = -star (q.1 ⟨(b, a), h⟩) := by
  simp [skewOf, G.strictUpper, h, not_lt.mpr h.le, (ne_of_lt h).symm]

theorem skewOf_coords {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = -S) : skewOf (skewCoords S) = S := by
  ext a b
  rcases lt_trichotomy a b with h | rfl | h
  · rw [skewOf_apply_lt _ _ _ h]
    rfl
  · rw [skewOf_apply_diag]
    have h1 : star (S a a) = -S a a := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS a) a
    have h2 := congrArg Complex.re h1
    simp at h2
    apply Complex.ext
    · simp
      linarith
    · simp [skewCoords]
  · rw [skewOf_apply_gt _ _ _ h]
    have h1 : star (S b a) = -S a b := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS a) b
    simp only [skewCoords]
    rw [h1, neg_neg]

theorem wMat_mul_wMat_mul {m : Type*} (n : ℕ) (X : Matrix (Fin n) m ℂ) : G.wMat n * (G.wMat n * X) = X := by
  rw [← Matrix.mul_assoc, wMat_mul_self, Matrix.one_mul]

theorem hpk_mul_hpk_mul {m : Type*} (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) m ℂ) : Hpk k r * (Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]

theorem rn_of (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (S : Matrix (Fin j) (Fin j) ℂ) (hS : Sᴴ = -S) :
    Rn k j ρ (Matrix.of.symm c, skewCoords S) = blk3 1 (-(G.wMat j * cᴴ * Hpk k ρ))
      (G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * Hpk k ρ * c) + S)) 0 1 c 0 0 1 := by
  rw [rn_eq]
  simp only [Equiv.apply_symm_apply, skewOf_coords S hS]

theorem bigCell_exists (g : B.Mat k (j + ρ)) (hg : g ∈ B.GV k (j + ρ)) (hD : DjU k j ρ g ≠ 0) :
    ∃ (x x' : RC k j ρ) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ), Z.det ≠ 0 ∧ γ ∈ B.GV k ρ ∧
      g = (Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x' := by
  obtain ⟨FourierUniquenessMirabolic, WeakApproximationGL, WhittakerVanishingImpliesZero, G21, G22, G23, G31, ContDiffOnLocalExtension, G33, rfl⟩ : ∃ FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33,
      g = blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33 := ⟨_, _, _, _, _, _, _, _, _, block3_eta g⟩
  have hg1 : (blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33)ᴴ * Hpk k (j + ρ) * blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33 =
      Hpk k (j + ρ) := hg
  have hg2 := unitary_right _ hg1
  have e11 : G31ᴴ * G.wMat j * FourierUniquenessMirabolic + G21ᴴ * Hpk k ρ * G21 + FourierUniquenessMirabolicᴴ * G.wMat j * G31 = 0 := by
    have h := hg1
    rw [block3_conjTranspose, hpkBlocks, block3_mul, block3_mul, block3_eq_iff] at h
    simpa using h.1
  have f33 : G33 * G.wMat j * G31ᴴ + ContDiffOnLocalExtension * Hpk k ρ * ContDiffOnLocalExtensionᴴ + G31 * G.wMat j * G33ᴴ = 0 := by
    have h := hg2
    rw [block3_conjTranspose, hpkBlocks, block3_mul, block3_mul, block3_eq_iff] at h
    simpa using h.2.2.2.2.2.2.2.2
  have hC : IsUnit G31.det := by
    have : DjU k j ρ (blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33) = (G.wMat j * G31).det := by
      unfold DjU; rw [hat_z_of_block3]
    rw [this, Matrix.det_mul] at hD
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hD)
  obtain ⟨Ci, hCi_def⟩ : ∃ Ci, Ci = G31⁻¹ := ⟨_, rfl⟩
  have hCi : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), Ci * (G31 * X) = X := by
    intro m X; rw [hCi_def, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul]
  have hCi' : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), G31 * (Ci * X) = X := by
    intro m X; rw [hCi_def, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hC, Matrix.one_mul]
  have hCiH : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), G31ᴴ * (Ciᴴ * X) = X := by
    intro m X; rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hCi_def, Matrix.nonsing_inv_mul _ hC,
      Matrix.conjTranspose_one, Matrix.one_mul]
  have hCiH' : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), Ciᴴ * (G31ᴴ * X) = X := by
    intro m X; rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hCi_def, Matrix.mul_nonsing_inv _ hC,
      Matrix.conjTranspose_one, Matrix.one_mul]

  obtain ⟨a', ha'⟩ : ∃ a', a' = Ci * ContDiffOnLocalExtension := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = Ci * G33 := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ, c' = -(Hpk k ρ * a'ᴴ * G.wMat j) := ⟨_, rfl⟩
  obtain ⟨S', hS'_def⟩ : ∃ S', S' = G.wMat j * b' + (1 / 2 : ℂ) • (c'ᴴ * Hpk k ρ * c') := ⟨_, rfl⟩
  have hS' : S'ᴴ = -S' := by
    apply eq_neg_of_add_eq_zero_right
    have h0 : G.wMat j * (Ci * ((G33 * G.wMat j * G31ᴴ + ContDiffOnLocalExtension * Hpk k ρ * ContDiffOnLocalExtensionᴴ + G31 * G.wMat j * G33ᴴ) *
        (Ciᴴ * G.wMat j))) = 0 := by rw [f33]; simp
    rw [← h0, hS'_def, hb', hc', ha']
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, hCi, hCiH]
    have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [h2]
    module
  have hRx' : Rn k j ρ (Matrix.of.symm c', skewCoords S') = blk3 1 a' b' 0 1 c' 0 0 1 := by
    rw [rn_of c' S' hS']
    congr 1
    · rw [hc']
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul]
    · rw [hS'_def]
      simp only [Matrix.mul_add, Matrix.mul_smul, wMat_mul_wMat_mul]
      module

  obtain ⟨c, hc⟩ : ∃ c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ, c = -(G21 * Ci) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = -(G.wMat j * cᴴ * Hpk k ρ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = a * c - FourierUniquenessMirabolic * Ci := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S, S = G.wMat j * b + (1 / 2 : ℂ) • (cᴴ * Hpk k ρ * c) := ⟨_, rfl⟩
  have hC1 : Ci * G31 = 1 := by rw [hCi_def]; exact Matrix.nonsing_inv_mul _ hC
  have hC2 : G31 * Ci = 1 := by rw [hCi_def]; exact Matrix.mul_nonsing_inv _ hC
  have hC3 : G31ᴴ * Ciᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hC1, Matrix.conjTranspose_one]
  have hC4 : Ciᴴ * G31ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hC2, Matrix.conjTranspose_one]
  have hS : Sᴴ = -S := by
    apply eq_neg_of_add_eq_zero_right
    have h0 : -(Ciᴴ * ((G31ᴴ * G.wMat j * FourierUniquenessMirabolic + G21ᴴ * Hpk k ρ * G21 + FourierUniquenessMirabolicᴴ * G.wMat j * G31) * Ci)) = 0 := by
      rw [e11]; simp
    rw [← h0, hS_def, hb, ha, hc]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hCi, hCiH, hCi', hCiH', hC1, hC2, hC3, hC4]
    have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [h2]
    module
  have hRx : Rn k j ρ (Matrix.of.symm c, skewCoords S) = blk3 1 a b 0 1 c 0 0 1 := by
    rw [rn_of c S hS]
    congr 1
    · rw [ha]
    · rw [hS_def]
      simp only [Matrix.mul_add, Matrix.mul_smul, wMat_mul_wMat_mul]
      module
  obtain ⟨product_first_partition, sizeConstantAtParamsWeight, flipOneThree, placeRankTwoOne, TaylorLogMetric, flipTwoThree, BlochKatoReduction, SumRepresentations, ArithmeticCylinders, hm⟩ : ∃ product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders,
      Rn k j ρ (Matrix.of.symm c, skewCoords S) * blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33 *
        (Rn k j ρ (Matrix.of.symm c', skewCoords S'))⁻¹ = blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders :=
    ⟨_, _, _, _, _, _, _, _, _, block3_eta _⟩
  have hmU : (blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders)ᴴ * Hpk k (j + ρ) * blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders =
      Hpk k (j + ρ) := by
    have hU := Formalism.QuantumDeterminants.uHGroup _ (Hpk k (j + ρ)) (hpk_det k (j + ρ))
    have h1 := hU.2.1 _ (rn_unitary (Matrix.of.symm c, skewCoords S)) _ hg
    have h2 := hU.2.1 _ h1 _ (hU.2.2 _ (rn_unitary (Matrix.of.symm c', skewCoords S'))).2
    rw [hm] at h2
    exact h2
  have hm2 := hm
  rw [hRx, hRx', uni_inv, block3_mul, block3_mul, block3_eq_iff] at hm2
  obtain ⟨h11, h12, h13, h21, h22, h23, h31, h32, h33⟩ := hm2
  simp at h11 h21 h31 h32 h33
  have hP11 : product_first_partition = 0 := by
    rw [← h11, hb, hc]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hC1]
    abel
  have hP21 : placeRankTwoOne = 0 := by
    rw [← h21, hc]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hC1]
    abel
  have hP32 : SumRepresentations = 0 := by
    rw [← h32, ha']
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hCi']
    abel
  have hP33 : ArithmeticCylinders = 0 := by
    rw [← h33, ha', hb']
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hCi']
    abel
  subst hP11 hP21 hP32 hP33 h31
  have hmU2 := hmU
  rw [block3_conjTranspose, hpkBlocks, block3_mul, block3_mul, block3_eq_iff] at hmU2
  obtain ⟨u11, u12, u13, u21, u22, u23, u31, u32, u33⟩ := hmU2
  simp at u11 u12 u13 u21 u22 u23 u31 u32 u33
  have hW : IsUnit (G31ᴴ * G.wMat j).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact (hC.star).mul (wMat_det j)
  have hP12 : sizeConstantAtParamsWeight = 0 := cancel_left _ _ hW u12
  have hγ : TaylorLogMetric ∈ B.GV k ρ := u22
  have hV : IsUnit (TaylorLogMetricᴴ * Hpk k ρ).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact ((gv_det hγ).star).mul (hpk_det k ρ)
  have hP23 : flipTwoThree = 0 := cancel_left _ _ hV u23
  have hP13 : flipOneThree = (G.wMat j * G31)ᴴ⁻¹ * G.wMat j := by
    rw [Matrix.conjTranspose_mul, wMat_conjTranspose]
    have := congrArg ((G31ᴴ * G.wMat j)⁻¹ * ·) u13
    rw [← this, ← Matrix.mul_assoc (G31ᴴ * G.wMat j)⁻¹ (G31ᴴ * G.wMat j) flipOneThree, Matrix.nonsing_inv_mul _ hW,
      Matrix.one_mul]
  subst hP12 hP23
  have hZ : (G.wMat j * G31).det ≠ 0 := by
    rw [Matrix.det_mul]; exact ((wMat_det j).mul hC).ne_zero
  refine ⟨(Matrix.of.symm c, skewCoords S), (Matrix.of.symm c', skewCoords S'), G.wMat j * G31, TaylorLogMetric, hZ, hγ, ?_⟩
  have hmm : mMap k j ρ (G.wMat j * G31) TaylorLogMetric = blk3 0 0 flipOneThree 0 TaylorLogMetric 0 G31 0 0 := by
    unfold mMap
    rw [hP13, wMat_mul_wMat_mul]
  rw [hmm, ← hm]
  simp only [← Matrix.mul_assoc, rn_inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, rn_inv_mul, Matrix.mul_one]

theorem bigCellBij : BigCellBij := by
  intro k j ρ g hg hD
  obtain ⟨x, x', Z, γ, hZ, hγ, hgeq⟩ := bigCell_exists g hg hD
  refine ⟨((x, x'), (Z, γ)), ⟨hZ, hγ, hgeq⟩, ?_⟩
  rintro ⟨⟨y, y'⟩, ⟨Z', γ'⟩⟩ ⟨hZ', hγ', hgeq'⟩
  obtain ⟨h1, h2, h3, h4⟩ := bigCell_uniq y y' x x' Z' Z γ' γ hZ' hZ hγ (hgeq'.symm.trans hgeq)
  simp only [h1, h2, h3, h4]

end Formalism.FourierDecayAlt.P.Ux3

namespace Formalism.FourierDecayAlt.P

theorem hat_z_on_slice : Formalism.FourierDecayAlt.U.ZhSlice := Ux3.zhSlice

theorem level_determinant_z : Formalism.FourierDecayAlt.U.DetZj := Ux3.detZj

theorem hat_z_minimum_degree : Formalism.FourierDecayAlt.U.ZhDmin := Ux3.zhDmin

theorem level_function_slice : Formalism.FourierDecayAlt.U.GfSlice := Ux3.gfSlice

theorem big_cell_bijection : Formalism.FourierDecayAlt.U.BigCellBij := Ux3.bigCellBij

end Formalism.FourierDecayAlt.P
