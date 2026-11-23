import Formalism.HermitianCurvature.StatementU

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Ux4

section blocks

variable {k j ρ : ℕ}

theorem block_index_first_val_eq (a : Fin j) : ((eB k j ρ) (Sum.inl (Sum.inl a))).val = a.val := by
  simp [eB]

theorem block_index_middle_val_eq (v : Fin (2 * ρ + k + 1)) : ((eB k j ρ) (Sum.inl (Sum.inr v))).val = j + v.val := by
  simp [eB]

theorem block_index_last_val_eq (a : Fin j) : ((eB k j ρ) (Sum.inr a)).val = j + (2 * ρ + k + 1) + a.val := by
  simp [eB]

theorem block3_apply
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (x y : Ix k j ρ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33 x y := by
  simp [blk3, Matrix.reindex_apply]

theorem ext_eB {M N : B.Mat k (j + ρ)} (h : ∀ x y : Ix k j ρ, M (eB k j ρ x) (eB k j ρ y) = N (eB k j ρ x) (eB k j ρ y)) :
    M = N := by
  ext a b
  simpa using h ((eB k j ρ).symm a) ((eB k j ρ).symm b)

theorem block3_mul
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 * blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 * ToralGalois + A12 * B21 + A13 * B31) (A11 * cocyclesToWachVectorsExponent + A12 * B22 + A13 * B32) (A11 * B13 + A12 * B23 + A13 * B33)
        (A21 * ToralGalois + A22 * B21 + A23 * B31) (A21 * cocyclesToWachVectorsExponent + A22 * B22 + A23 * B32) (A21 * B13 + A22 * B23 + A23 * B33)
        (A31 * ToralGalois + A32 * B21 + A33 * B31) (A31 * cocyclesToWachVectorsExponent + A32 * B22 + A33 * B32) (A31 * B13 + A32 * B23 + A33 * B33) := by
  simp only [blk3, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  ext ((a | a) | a) ((b | b) | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply] <;> ring

theorem block3_one : (1 : B.Mat k (j + ρ)) = blk3 (k := k) (j := j) (ρ := ρ) 1 0 0 0 1 0 0 0 1 := by
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;>
    simp [Matrix.one_apply, (eB k j ρ).injective.eq_iff]

theorem block_three_zero_size_eq : blk3 (k := k) (j := j) (ρ := ρ) 0 0 0 0 0 0 0 0 0 = 0 := by
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp

theorem block3_add
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 + blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 + ToralGalois) (A12 + cocyclesToWachVectorsExponent) (A13 + B13) (A21 + B21) (A22 + B22) (A23 + B23) (A31 + B31) (A32 + B32) (A33 + B33) := by
  apply ext_eB
  intro x y
  rw [Matrix.add_apply, block3_apply, block3_apply, block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp

theorem block3_conjTranspose
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33)ᴴ =
      blk3 A11ᴴ A21ᴴ A31ᴴ A12ᴴ A22ᴴ A32ᴴ A13ᴴ A23ᴴ A33ᴴ := by
  apply ext_eB
  intro x y
  rw [Matrix.conjTranspose_apply, block3_apply, block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp [Matrix.conjTranspose_apply]

theorem block3_lower_blocks_zero
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (h21 : A21 = 0) (h31 : A31 = 0) (i b : Fin (2 * (j + ρ) + k + 1)) (hb : b.val < j) (hi : j ≤ i.val) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 i b = 0 := by
  obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨y, rfl⟩ := (eB k j ρ).surjective b
  rw [block3_apply]
  rcases y with ((c | c) | c)
  · rcases x with ((a | a) | a)
    · rw [block_index_first_val_eq] at hi
      exact absurd hi (not_le.2 a.isLt)
    · simp [h21]
    · simp [h31]
  · rw [block_index_middle_val_eq] at hb
    omega
  · rw [block_index_last_val_eq] at hb
    omega

theorem wMat_mul_self (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext a b
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a.rev]
  · by_cases h : a = b
    · subst h
      simp [Fin.rev_rev]
    · have h' : b ≠ a.rev.rev := by rw [Fin.rev_rev]; exact Ne.symm h
      simp [h, h', Ne.symm h]
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wMat_conjTranspose (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by
  ext a b
  simp only [G.wMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : b = a.rev
  · subst h
    simp [Fin.rev_rev]
  · have h' : a ≠ b.rev := by
      intro h'
      apply h
      rw [h', Fin.rev_rev]
    simp [h, h']

theorem hpk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Hpk]
  by_cases hab : a = b
  · subst hab
    split_ifs <;> simp
  · have hba : b ≠ a := Ne.symm hab
    have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    simp only [hab, hba, and_false, if_false]
    split_ifs <;> first | (exfalso; omega) | simp

theorem hpkBlocks : HpkBlocks := by
  intro k j ρ
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;>
  · have ha := a.isLt
    have hb := b.isLt
    simp only [Hpk, G.wMat, Fin.ext_iff, block_index_first_val_eq, block_index_middle_val_eq, block_index_last_val_eq, Fin.val_rev, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply]
    split_ifs <;> first | rfl | (exfalso; omega)

end blocks

section rad

variable {k j ρ : ℕ}

theorem w_w_mul (M : Matrix (Fin j) (Fin j) ℂ) : G.wMat j * (G.wMat j * M) = M := by
  rw [← Matrix.mul_assoc, wMat_mul_self, Matrix.one_mul]

theorem w_w_mul' {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) : G.wMat j * (G.wMat j * M) = M := by
  rw [← Matrix.mul_assoc, wMat_mul_self, Matrix.one_mul]

noncomputable def RnInv (x : RC k j ρ) : B.Mat k (j + ρ) :=
  blk3 1 (G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ)
    (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 -
      G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2))
    0 1 (-(Matrix.of x.1)) 0 0 1

theorem Rn_mul_RnInv (x : RC k j ρ) : Rn k j ρ x * RnInv x = 1 := by
  rw [Rn, RnInv, block3_mul, block3_one]
  congr 1 <;>
    simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, neg_neg, smul_zero, sub_zero, neg_zero, zero_sub] <;> abel

theorem Rn_inv_eq (x : RC k j ρ) : (Rn k j ρ x)⁻¹ = RnInv x := Matrix.inv_eq_right_inv (Rn_mul_RnInv x)

theorem Rn_mul_inv (x : RC k j ρ) : Rn k j ρ x * (Rn k j ρ x)⁻¹ = 1 := by
  rw [Rn_inv_eq, Rn_mul_RnInv]

theorem mMap_mul_embG (Z : Matrix (Fin j) (Fin j) ℂ) (γ y : B.Mat k ρ) :
    mMap k j ρ Z γ * embG k j ρ y = mMap k j ρ Z (γ * y) := by
  unfold mMap embG
  rw [block3_mul]
  congr 1 <;> simp

theorem embG_mul_mMap (Z : Matrix (Fin j) (Fin j) ℂ) (γ y : B.Mat k ρ) :
    embG k j ρ y * mMap k j ρ Z γ = mMap k j ρ Z (y * γ) := by
  unfold mMap embG
  rw [block3_mul]
  congr 1 <;> simp

theorem mMap_mul_muP (Z W : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) :
    mMap k j ρ Z γ * muP k j ρ W = mMap k j ρ (Z * W) γ := by
  unfold mMap muP
  rw [block3_mul]
  congr 1 <;> simp [Matrix.mul_assoc, w_w_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev]

end rad

theorem symmetricScalarBlockMatrix_mul {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' = blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block2_det_upper_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    (blk2 A B 0 D).det = A.det * D.det := by
  rw [blk2, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem zj_mul {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z q : Matrix (Fin s) (Fin s) ℂ) :
    Zj a b H (Z * q) = Zj a b H Z * ((blk2 1 (Matrix.of b) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of b) 0 1) := by
  have hU : blk2 1 (Matrix.of b) 0 1 * (blk2 1 (Matrix.of b) 0 1)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [block2_det_upper_triangular]; simp)
  have hD : blk2 H 0 0 (Z * q) = blk2 H 0 0 Z * blk2 1 0 0 q := by
    rw [symmetricScalarBlockMatrix_mul]; simp
  unfold Zj
  rw [hD]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (blk2 1 (Matrix.of b) 0 1) (blk2 1 (Matrix.of b) 0 1)⁻¹, hU, Matrix.one_mul]

theorem ux_zjAffine : ZjAffine := by
  intro p s a b H CC
  unfold Zj
  rw [symmetricScalarBlockMatrix_mul, symmetricScalarBlockMatrix_mul]
  simp

end Formalism.FourierDecayAlt.P.Ux4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Ux4

theorem slice_right_coordinates : Formalism.FourierDecayAlt.U.SliceRight := by
  intro k p s ρ σ d ξ Z γ y
  unfold gaXi
  rw [← mMap_mul_embG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.2) (Rn k (p + s) ρ ξ.1.2)⁻¹, Rn_mul_inv, Matrix.one_mul]

theorem slice_left_coordinates : Formalism.FourierDecayAlt.U.SliceLeft := by
  intro k p s ρ σ d ξ Z γ y
  unfold gaXi
  rw [← embG_mul_mMap]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.1) (Rn k (p + s) ρ ξ.1.1)⁻¹, Rn_mul_inv, Matrix.one_mul]

theorem slice_z_coordinates : Formalism.FourierDecayAlt.U.SliceZ := by
  intro k p s ρ σ d ξ Z q γ
  unfold gaXi
  have hZ : ZjH σ d ξ.2 (Matrix.of Z * q) = ZjH σ d ξ.2 Z *
      ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of ξ.2.1.2) 0 1) := by
    unfold ZjH
    exact zj_mul _ _ _ _ _
  rw [hZ, ← mMap_mul_muP]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.2) (Rn k (p + s) ρ ξ.1.2)⁻¹, Rn_mul_inv, Matrix.one_mul]

theorem level_z_affine : Formalism.FourierDecayAlt.U.ZjAffine := ux_zjAffine

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Ux4

section lie

variable {k j ρ : ℕ}

theorem skewOf_conjTranspose (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  unfold skewOf
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  have : (star fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) = (fun i => -(Complex.I * ((q.2 i : ℝ) : ℂ))) := by
    funext i
    simp [Complex.conj_ofReal]
  rw [this, ← Matrix.diagonal_neg]
  abel

theorem Rn_unitary (x : RC k j ρ) : (Rn k j ρ x)ᴴ * Hpk k (j + ρ) * Rn k j ρ x = Hpk k (j + ρ) := by
  rw [hpkBlocks k j ρ]
  unfold Rn
  rw [block3_conjTranspose, block3_mul, block3_mul]
  have hw := wMat_conjTranspose j
  have hH := hpk_conjTranspose k ρ
  have hS := skewOf_conjTranspose x.2
  congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, hw, hH, hS,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, w_w_mul, w_w_mul', wMat_mul_self,
    neg_zero, neg_add_cancel, Matrix.smul_mul, star_neg, star_div₀, star_one, star_ofNat]
  all_goals module

theorem conj_lie {N : ℕ} (n M H : Matrix (Fin N) (Fin N) ℂ) (hu : nᴴ * H * n = H) (hH : Hᴴ = H)
    (hn : n * n⁻¹ = 1) (hM : Mᴴ * H + H * M = 0) :
    (n⁻¹ * M * n)ᴴ * H + H * (n⁻¹ * M * n) = 0 := by
  have h1 : H * n⁻¹ = nᴴ * H := by
    calc H * n⁻¹ = nᴴ * H * n * n⁻¹ := by rw [hu]
      _ = nᴴ * H := by rw [Matrix.mul_assoc (nᴴ * H), hn, Matrix.mul_one]
  have h2 : (n⁻¹)ᴴ * H = H * n := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hH] using this
  calc (n⁻¹ * M * n)ᴴ * H + H * (n⁻¹ * M * n) = nᴴ * Mᴴ * ((n⁻¹)ᴴ * H) + (H * n⁻¹) * M * n := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = nᴴ * (Mᴴ * H + H * M) * n := by
        rw [h2, h1]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hM]; simp

theorem lie_Y (Y : B.Mat k ρ) (hY : B.inLie k ρ Y) :
    B.inLie k (j + ρ) (blk3 0 0 0 0 Y 0 0 0 0) := by
  unfold B.inLie at hY ⊢
  rw [hpkBlocks k j ρ, block3_conjTranspose, block3_mul, block3_mul, block3_add, ← block_three_zero_size_eq]
  congr 1 <;> simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_zero, hY]

theorem lie_Q (Q : Matrix (Fin j) (Fin j) ℂ) :
    B.inLie k (j + ρ) (blk3 (k := k) (ρ := ρ) Q 0 0 0 0 0 0 0 (-(G.wMat j * Qᴴ * G.wMat j))) := by
  unfold B.inLie
  have hw := wMat_conjTranspose j
  rw [hpkBlocks k j ρ, block3_conjTranspose, block3_mul, block3_mul, block3_add, ← block_three_zero_size_eq]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hw, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, w_w_mul, wMat_mul_self, add_neg_cancel]
  all_goals abel

end lie

end Formalism.FourierDecayAlt.P.Ux4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Ux4

theorem directions_in_parabolic : Formalism.FourierDecayAlt.U.DirectionsInP := by
  intro k j ρ x
  have hn := Rn_mul_inv x
  constructor
  · intro Y hY
    refine ⟨conj_lie _ _ _ (Rn_unitary x) (hpk_conjTranspose k (j + ρ)) hn (lie_Y Y hY), ?_⟩
    intro i b hb hi
    rw [Rn_inv_eq]
    unfold RnInv Rn
    rw [block3_mul, block3_mul]
    exact block3_lower_blocks_zero _ _ _ _ _ _ _ _ _ (by simp) (by simp) i b hb hi
  · intro Q
    refine ⟨conj_lie _ _ _ (Rn_unitary x) (hpk_conjTranspose k (j + ρ)) hn (lie_Q Q), ?_⟩
    intro i b hb hi
    rw [Rn_inv_eq]
    unfold RnInv Rn
    rw [block3_mul, block3_mul]
    exact block3_lower_blocks_zero _ _ _ _ _ _ _ _ _ (by simp) (by simp) i b hb hi

end Formalism.FourierDecayAlt.P
