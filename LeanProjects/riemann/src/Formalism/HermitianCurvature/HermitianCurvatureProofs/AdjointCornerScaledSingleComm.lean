import Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section blocks

variable {j : ℕ}

theorem zfull_conjTranspose (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) :
    (zfull Z τ)ᴴ = zfull Zᴴ (star τ) := by
  ext a b
  rw [Matrix.conjTranspose_apply, zfull_apply, zfull_apply]
  by_cases h1 : a.val < j ∧ b.val < j
  · rw [dif_pos ⟨h1.2, h1.1⟩, dif_pos h1, Matrix.conjTranspose_apply]
  · rw [dif_neg (by tauto), dif_neg h1]
    by_cases h2 : a.val = j ∧ b.val = j
    · rw [if_pos ⟨h2.2, h2.1⟩, if_pos h2]
    · rw [if_neg (by tauto), if_neg h2, star_zero]

theorem zfull_mul (Z W : Matrix (Fin j) (Fin j) ℂ) (τ σ : ℂ) :
    zfull Z τ * zfull W σ = zfull (Z * W) (τ * σ) := by
  unfold zfull U.blk2
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 2
  ext a b
  simp [Matrix.mul_apply]

theorem zfull_one : zfull (1 : Matrix (Fin j) (Fin j) ℂ) 1 = 1 := by
  ext a b
  rw [zfull_apply, Matrix.one_apply]
  by_cases h1 : a.val < j ∧ b.val < j
  · rw [dif_pos h1, Matrix.one_apply]
    simp [Fin.ext_iff]
  · rw [dif_neg h1]
    by_cases h2 : a.val = j ∧ b.val = j
    · rw [if_pos h2, if_pos (Fin.ext (by omega))]
    · rw [if_neg h2, if_neg]
      intro h; apply h2; subst h; have := a.isLt; omega

theorem zfull_inv {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) :
    (zfull Z τ)⁻¹ = zfull Z⁻¹ τ⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [zfull_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hZ), inv_mul_cancel₀ hτ, zfull_one]

theorem zfull_conjTranspose_inv {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) :
    ((zfull Z τ)ᴴ)⁻¹ = zfull (Zᴴ)⁻¹ (star τ)⁻¹ := by
  rw [zfull_conjTranspose, zfull_inv (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hZ)
    (star_ne_zero.mpr hτ)]

end blocks

section units

variable {k r j : ℕ}

theorem cast_eB_surj (hj : j + 1 ≤ r) (p : Fin (2 * r + k + 1)) :
    ∃ P : U.Ix k (j + 1) (r - (j + 1)), p = Fin.cast (by omega) (U.eB k (j + 1) (r - (j + 1)) P) := by
  obtain ⟨P, hP⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) p)
  exact ⟨P, by rw [hP]; rfl⟩

theorem single_eI_blk (hj : j + 1 ≤ r) (x y : Fin (j + 1)) :
    Matrix.single (eI k r ⟨x.val, by omega⟩) (eI k r ⟨y.val, by omega⟩) (1 : ℂ) =
      D.castM (by omega : j + 1 + (r - (j + 1)) = r) (U.blk3 (Matrix.single x y 1) 0 0 0 0 0 0 0 0) := by
  ext p q
  obtain ⟨P, rfl⟩ := cast_eB_surj (k := k) hj p
  obtain ⟨Q, rfl⟩ := cast_eB_surj (k := k) hj q
  rw [LeftFubiniLemmas.castM_apply']
  simp only [Fin.cast_cast, Fin.cast_eq_self]
  rw [Ux3.block3_apply]
  rcases P with ((a | a) | a) <;> rcases Q with ((b | b) | b) <;>
    simp [Matrix.single_apply, eI, Fin.ext_iff, Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] <;> omega

theorem single_esI_blk (hj : j + 1 ≤ r) (x y : Fin (j + 1)) :
    Matrix.single (esI k r ⟨x.val, by omega⟩) (esI k r ⟨y.val, by omega⟩) (1 : ℂ) =
      D.castM (by omega : j + 1 + (r - (j + 1)) = r) (U.blk3 0 0 0 0 0 0 0 0 (Matrix.single x.rev y.rev 1)) := by
  ext p q
  obtain ⟨P, rfl⟩ := cast_eB_surj (k := k) hj p
  obtain ⟨Q, rfl⟩ := cast_eB_surj (k := k) hj q
  rw [LeftFubiniLemmas.castM_apply']
  simp only [Fin.cast_cast, Fin.cast_eq_self]
  rw [Ux3.block3_apply]
  rcases P with ((a | a) | a) <;> rcases Q with ((b | b) | b) <;>
    simp [Matrix.single_apply, esI, Fin.ext_iff, Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val, Fin.val_rev] <;>
    (try omega) <;>
    (have := x.isLt; have := y.isLt; have := a.isLt; have := b.isLt; split_ifs <;> first | rfl | omega)

end units

section linear

variable {k j ρ : ℕ}

theorem smul_block_three (c : ℂ) (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin j) (Fin j) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A31 : Matrix (Fin j) (Fin j) ℂ)
    (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    c • U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 =
      U.blk3 (c • A11) (c • A12) (c • A13) (c • A21) (c • A22) (c • A23) (c • A31) (c • A32) (c • A33) := by
  refine Ux4.ext_eB fun x y => ?_
  rw [Matrix.smul_apply, Ux3.block3_apply, Ux3.block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp

theorem castM_add' {a b : ℕ} (h : a = b) (M N : B.Mat k a) : D.castM h (M + N) = D.castM h M + D.castM h N := by
  ext p q; rfl

theorem castM_smul' {a b : ℕ} (h : a = b) (c : ℂ) (M : B.Mat k a) : D.castM h (c • M) = c • D.castM h M := by
  ext p q; rfl

theorem castM_sub' {a b : ℕ} (h : a = b) (M N : B.Mat k a) : D.castM h (M - N) = D.castM h M - D.castM h N := by
  ext p q; rfl

theorem castM_sum' {a b : ℕ} (h : a = b) {ι : Type*} (s : Finset ι) (M : ι → B.Mat k a) :
    D.castM h (∑ i ∈ s, M i) = ∑ i ∈ s, D.castM h (M i) := by
  ext p q
  simp only [LeftFubiniLemmas.castM_apply', Matrix.sum_apply]

end linear

section conjug

variable {k r j : ℕ}

theorem level_point_eq_block_three (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) :
    x0 k r j hj Z τ γ = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 0 0 (((zfull Z τ)ᴴ)⁻¹ * G.wMat (j + 1)) 0 γ 0 (G.wMat (j + 1) * zfull Z τ) 0 0) := rfl

def hM (k r j : ℕ) (hj : j + 1 ≤ r) (x y : Fin (j + 1)) (s : ℂ) : B.Mat k r :=
  s • Matrix.single (eI k r ⟨x.val, by omega⟩) (eI k r ⟨y.val, by omega⟩) (1 : ℂ) -
    star s • Matrix.single (esI k r ⟨y.val, by omega⟩) (esI k r ⟨x.val, by omega⟩) (1 : ℂ)

theorem hM_blk (hj : j + 1 ≤ r) (x y : Fin (j + 1)) (s : ℂ) :
    hM k r j hj x y s = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 (s • Matrix.single x y 1) 0 0 0 0 0 0 0 (-(star s) • Matrix.single y.rev x.rev 1)) := by
  unfold hM
  rw [single_eI_blk hj, single_esI_blk hj, ← castM_smul', ← castM_smul', ← castM_sub', smul_block_three, smul_block_three]
  congr 1
  refine Ux4.ext_eB fun p q => ?_
  rw [Matrix.sub_apply, Ux3.block3_apply, Ux3.block3_apply, Ux3.block3_apply]
  rcases p with ((a | a) | a) <;> rcases q with ((b | b) | b) <;> simp [neg_smul]

def nN (k r j : ℕ) (hj : j + 1 ≤ r) (a : Fin j → ℂ) : B.Mat k r :=
  ∑ b : Fin j, (a b • Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ))

theorem nL_eq (hj : j + 1 ≤ r) (a : Fin j → ℂ) : nL k r j hj a = 1 + nN k r j hj a := rfl

theorem nN_blk (hj : j + 1 ≤ r) (a : Fin j → ℂ) :
    nN k r j hj a = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 (-∑ b : Fin j, conj (a b) • Matrix.single b.castSucc (Fin.last j) 1) 0 0 0 0 0 0 0
        (∑ b : Fin j, a b • Matrix.single (Fin.last j).rev b.castSucc.rev 1)) := by
  unfold nN
  have e1 : ∀ b : Fin j, Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) =
      Matrix.single (esI k r ⟨(Fin.last j).val, by simp; omega⟩) (esI k r ⟨(b.castSucc : Fin (j + 1)).val, by simp; omega⟩) 1 :=
    fun b => rfl
  have e2 : ∀ b : Fin j, Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ) =
      Matrix.single (eI k r ⟨(b.castSucc : Fin (j + 1)).val, by simp; omega⟩) (eI k r ⟨(Fin.last j).val, by simp; omega⟩) 1 :=
    fun b => rfl
  simp_rw [e1, e2, single_eI_blk hj, single_esI_blk hj, ← castM_smul', ← castM_sub', ← castM_sum']
  congr 1
  refine Ux4.ext_eB fun p q => ?_
  rw [Ux3.block3_apply, Matrix.sum_apply]
  simp_rw [Matrix.sub_apply, Matrix.smul_apply, Ux3.block3_apply]
  rcases p with ((c | c) | c) <;> rcases q with ((d | d) | d) <;>
    simp [Matrix.sum_apply, Matrix.single_apply]

end conjug

section blk2alg

variable {j : ℕ}

theorem castM_mul' {k a b : ℕ} (h : a = b) (M N : B.Mat k a) : D.castM h (M * N) = D.castM h M * D.castM h N := by
  subst h; simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem symmetricScalarBlockMatrix_mul {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    U.blk2 A B C D * U.blk2 A' B' C' D' = U.blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold U.blk2
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem smul_block_two {p s : ℕ} (c : ℂ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    c • U.blk2 A B C D = U.blk2 (c • A) (c • B) (c • C) (c • D) := by
  unfold U.blk2
  rw [← Matrix.fromBlocks_smul]
  ext a b
  simp [Matrix.reindex_apply]

theorem sum_single_last (a : Fin j → ℂ) :
    (∑ c : Fin j, a c • Matrix.single (Fin.last j) c.castSucc (1 : ℂ)) =
      U.blk2 0 0 (Matrix.of fun (_ : Fin 1) c => a c) 0 := by
  ext p q
  obtain ⟨p', rfl⟩ := finSumFinEquiv.surjective p
  obtain ⟨q', rfl⟩ := finSumFinEquiv.surjective q
  rw [Matrix.sum_apply]
  unfold U.blk2
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rcases p' with p' | p' <;> rcases q' with q' | q'
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h.1; simp at this; omega
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h.1; simp at this; omega
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
    rw [Finset.sum_eq_single q']
    · rw [if_pos]; constructor <;> ext <;> simp
    · intro c _ hc; rw [if_neg]; intro h; apply hc; have := congrArg Fin.val h.2; ext; simpa using this
    · simp
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h.2; simp at this; omega

theorem sum_single_col (a : Fin j → ℂ) :
    (∑ c : Fin j, a c • Matrix.single c.castSucc (Fin.last j) (1 : ℂ)) =
      U.blk2 0 (Matrix.of fun c (_ : Fin 1) => a c) 0 0 := by
  ext p q
  obtain ⟨p', rfl⟩ := finSumFinEquiv.surjective p
  obtain ⟨q', rfl⟩ := finSumFinEquiv.surjective q
  rw [Matrix.sum_apply]
  unfold U.blk2
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rcases p' with p' | p' <;> rcases q' with q' | q'
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h.2; simp at this; omega
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    rw [Finset.sum_eq_single p']
    · rw [if_pos]; constructor <;> ext <;> simp
    · intro c _ hc; rw [if_neg]; intro h; apply hc; have := congrArg Fin.val h.1; ext; simpa using this
    · simp
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h.1; simp at this; omega
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; intro h; have := congrArg Fin.val h.1; simp at this; omega

end blk2alg

section conjx0

variable {k r j : ℕ}

theorem single_last_eq_block_two (b : Fin j) :
    Matrix.single (Fin.last j) b.castSucc (1 : ℂ) = U.blk2 0 0 (Matrix.single 0 b 1) 0 := by
  have := sum_single_last (j := j) (fun c => if c = b then (1 : ℂ) else 0)
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  rw [this]
  congr 1
  ext u c
  fin_cases u
  simp [Matrix.single_apply, eq_comm]

theorem single_column_eq_block_two (b : Fin j) :
    Matrix.single b.castSucc (Fin.last j) (1 : ℂ) = U.blk2 0 (Matrix.single b 0 1) 0 0 := by
  have := sum_single_col (j := j) (fun c => if c = b then (1 : ℂ) else 0)
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  rw [this]
  congr 1
  ext c u
  fin_cases u
  simp [Matrix.single_apply, eq_comm]

theorem w_mul_single {n : ℕ} (x y : Fin n) : G.wMat n * Matrix.single x y (1 : ℂ) = Matrix.single x.rev y 1 := by
  ext a b
  rw [Ux3.wMat_mul_apply, Matrix.single_apply, Matrix.single_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by rw [h1, Fin.rev_rev], h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1, Fin.rev_rev], h2⟩

theorem single_mul_w {n : ℕ} (x y : Fin n) : Matrix.single x y (1 : ℂ) * G.wMat n = Matrix.single x y.rev 1 := by
  ext a b
  rw [Formalism.FourierDecayAlt.P.G5.mul_wMat_apply, Matrix.single_apply, Matrix.single_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, Fin.rev_rev]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h2, Fin.rev_rev]⟩

theorem weyl_corner_scaled_single_comm (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : Z.det ≠ 0) (τ s : ℂ) (b : Fin j) :
    G.wMat (j + 1) * zfull Z τ * (s • Matrix.single (Fin.last j) b.castSucc (1 : ℂ)) =
      (∑ c : Fin j, (s * τ * Z⁻¹ b c) • Matrix.single (Fin.last j).rev c.castSucc.rev (1 : ℂ)) *
        (G.wMat (j + 1) * zfull Z τ) := by
  have hw : G.wMat (j + 1) * G.wMat (j + 1) = 1 := Ux3.wMat_mul_self (j + 1)
  have e1 : ∀ c : Fin j, Matrix.single (Fin.last j).rev c.castSucc.rev (1 : ℂ) =
      G.wMat (j + 1) * Matrix.single (Fin.last j) c.castSucc 1 * G.wMat (j + 1) := by
    intro c; rw [w_mul_single, single_mul_w]
  simp_rw [e1]
  have e2 : (∑ c : Fin j, (s * τ * Z⁻¹ b c) • (G.wMat (j + 1) * Matrix.single (Fin.last j) c.castSucc (1 : ℂ) *
      G.wMat (j + 1))) * (G.wMat (j + 1) * zfull Z τ) =
      G.wMat (j + 1) * ((∑ c : Fin j, (s * τ * Z⁻¹ b c) • Matrix.single (Fin.last j) c.castSucc (1 : ℂ)) * zfull Z τ) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc (G.wMat (j + 1)) (G.wMat (j + 1)) (zfull Z τ), hw, Matrix.one_mul]
  rw [e2, Matrix.mul_assoc]
  congr 1
  rw [sum_single_last, single_last_eq_block_two, smul_block_two, smul_zero, smul_zero, smul_zero]
  unfold zfull
  rw [symmetricScalarBlockMatrix_mul, symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  have hinv : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z (isUnit_iff_ne_zero.mpr hZ)
  ext u v
  fin_cases u
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  have h3 : ∑ x : Fin j, s * τ * Z⁻¹ b x * Z x v = s * τ * (Z⁻¹ * Z) b v := by
    rw [Matrix.mul_apply, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  rw [h3, hinv, Matrix.one_apply]
  by_cases h : b = v
  · subst h; simp [mul_comm]
  · simp [h]

theorem adjoint_corner_scaled_single_comm (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : Z.det ≠ 0) (τ s : ℂ) (hτ : τ ≠ 0) (b : Fin j) :
    ((zfull Z τ)ᴴ)⁻¹ * G.wMat (j + 1) * (-(star s) • Matrix.single b.castSucc.rev (Fin.last j).rev (1 : ℂ)) =
      (-∑ c : Fin j, conj (s * τ * Z⁻¹ b c) • Matrix.single c.castSucc (Fin.last j) (1 : ℂ)) *
        (((zfull Z τ)ᴴ)⁻¹ * G.wMat (j + 1)) := by
  have e1 : G.wMat (j + 1) * Matrix.single b.castSucc.rev (Fin.last j).rev (1 : ℂ) =
      Matrix.single b.castSucc (Fin.last j) 1 * G.wMat (j + 1) := by
    rw [w_mul_single, single_mul_w, Fin.rev_rev]
  have lhs : ((zfull Z τ)ᴴ)⁻¹ * G.wMat (j + 1) * (-(star s) • Matrix.single b.castSucc.rev (Fin.last j).rev (1 : ℂ)) =
      -((star s • (((zfull Z τ)ᴴ)⁻¹ * Matrix.single b.castSucc (Fin.last j) (1 : ℂ))) * G.wMat (j + 1)) := by
    rw [Matrix.mul_smul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, Matrix.smul_mul, neg_smul]
  have rhs : (-∑ c : Fin j, conj (s * τ * Z⁻¹ b c) • Matrix.single c.castSucc (Fin.last j) (1 : ℂ)) *
      (((zfull Z τ)ᴴ)⁻¹ * G.wMat (j + 1)) =
      -(((∑ c : Fin j, conj (s * τ * Z⁻¹ b c) • Matrix.single c.castSucc (Fin.last j) (1 : ℂ)) *
        ((zfull Z τ)ᴴ)⁻¹) * G.wMat (j + 1)) := by
    rw [Matrix.neg_mul, Matrix.mul_assoc]
  rw [lhs, rhs]
  congr 2
  rw [zfull_conjTranspose_inv hZ hτ, sum_single_col, single_column_eq_block_two]
  unfold zfull
  rw [symmetricScalarBlockMatrix_mul, smul_block_two, symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_zero]
  congr 1
  ext u v
  fin_cases v
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.of_apply, smul_eq_mul,
    Fin.sum_univ_one]
  rw [Finset.sum_eq_single b]
  · have hτ' : star τ ≠ 0 := star_ne_zero.mpr hτ
    rw [if_pos ⟨rfl, Subsingleton.elim _ _⟩, mul_one, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply]
    simp only [map_mul, starRingEnd_apply]
    field_simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

end conjx0

section conjfinal

variable {k r j : ℕ}

theorem level_point_conj_unipotent (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} (hZ : Z.det ≠ 0) {τ : ℂ} (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) (b : Fin j) (s : ℂ) :
    x0 k r j hj Z τ γ * hM k r j hj (Fin.last j) b.castSucc s =
      nN k r j hj (fun c => s * τ * Z⁻¹ b c) * x0 k r j hj Z τ γ := by
  rw [level_point_eq_block_three, hM_blk, nN_blk, ← castM_mul', ← castM_mul']
  congr 1
  rw [Ux3.block3_mul, Ux3.block3_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [adjoint_corner_scaled_single_comm Z hZ τ s hτ b, weyl_corner_scaled_single_comm Z hZ τ s b]

end conjfinal

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
