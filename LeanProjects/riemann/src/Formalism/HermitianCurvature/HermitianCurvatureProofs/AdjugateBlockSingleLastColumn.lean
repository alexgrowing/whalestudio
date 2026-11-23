import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section blocks

theorem ptEntry_append (h l : C.LPt) (a b : ℕ) :
    D.ptEntry (h ++ l) a b =
      if a < D.ptSize h ∧ b < D.ptSize h then D.ptEntry h a b
      else if D.ptSize h ≤ a ∧ D.ptSize h ≤ b then D.ptEntry l (a - D.ptSize h) (b - D.ptSize h) else 0 := by
  induction h generalizing a b with
  | nil => simp [D.ptSize]
  | cons x rest ih =>
    obtain ⟨s, t⟩ := x
    have hs : D.ptSize ((s, t) :: rest) = s + D.ptSize rest := by simp [D.ptSize]
    rw [List.cons_append, hs]
    simp only [D.ptEntry, ih, Nat.sub_sub]
    split_ifs <;> first | rfl | (exfalso; omega) | omega | simp_all

theorem ptMatN_append_one (h : C.LPt) (ζ : ℂ) (j : ℕ) (hj : D.ptSize h = j) :
    D.ptMatN (h ++ [(1, ζ)]) (j + 1) =
      Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0) (Matrix.fromBlocks (D.ptMatN h j) 0 0 (Matrix.of fun _ _ => ζ)) := by
  ext a b
  obtain ⟨x, rfl⟩ := (Ux3.eC j 0).surjective a
  obtain ⟨y, rfl⟩ := (Ux3.eC j 0).surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, D.ptMatN]
  rcases x with x | x <;> rcases y with y | y
  · simp only [Matrix.fromBlocks_apply₁₁, ptEntry_append, Ux3.column_index_first_val, hj, x.isLt, y.isLt, and_self, if_true]
    rfl
  · simp only [Matrix.fromBlocks_apply₁₂, ptEntry_append, Ux3.column_index_first_val, Ux3.column_index_second_val, hj, Matrix.zero_apply]
    rw [if_neg (by omega), if_neg (by omega)]
  · simp only [Matrix.fromBlocks_apply₂₁, ptEntry_append, Ux3.column_index_first_val, Ux3.column_index_second_val, hj, Matrix.zero_apply]
    rw [if_neg (by omega), if_neg (by omega)]
  · have hx : x.val = 0 := by omega
    have hy : y.val = 0 := by omega
    simp only [Matrix.fromBlocks_apply₂₂, ptEntry_append, Ux3.column_index_second_val, hj, Matrix.of_apply]
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, hx, hy]
    simp [D.ptEntry]

end blocks

section zhat

variable {k j : ℕ}

theorem zhat_mMap (z z' : Fin (2 * (j + 0) + k + 1) → ℂ) (hz : inWb k (j + 0) z) (hz' : inWb k (j + 0) z')
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ0 : B.Mat k 0) :
    Zhat k (j + 0) z z' (mMap k j 0 Z γ0) =
      Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0)
        (Matrix.fromBlocks Z 0 0 (Zhat k 0 (lowV k j 0 z) (lowV k j 0 z') γ0)) := by
  unfold mMap
  rw [Ux3.z_hat_of_block3 z z' hz hz']
  congr 1
  rw [← Matrix.mul_assoc, Ux3.wMat_mul_self, Matrix.one_mul, Formalism.QuantumDeterminants.Zhat_eq]
  simp [Matrix.mul_assoc]

end zhat

section lift

variable {k j : ℕ}

theorem liftVec_eB (u : Fin (2 * 0 + k + 1) → ℂ) (x : Ix k j 0) :
    liftVec k j 0 u (eB k j 0 x) = Sum.elim (Sum.elim (fun _ => 0) u) (fun _ => 0) x := by
  rcases x with (a | b) | a
  · have h1 : (eB k j 0 (Sum.inl (Sum.inl a))).val = a.val := by simp [U.eB]
    have ha := a.isLt
    simp only [liftVec, Sum.elim_inl]
    rw [dif_neg (by rw [h1]; omega)]
  · have h1 : (eB k j 0 (Sum.inl (Sum.inr b))).val = j + b.val := by simp [U.eB]
    have hb := b.isLt
    simp only [liftVec, Sum.elim_inl, Sum.elim_inr]
    rw [dif_pos (by rw [h1]; omega)]
    congr 1
    ext
    simp [h1]
  · have h1 : (eB k j 0 (Sum.inr a)).val = j + (2 * 0 + k + 1) + a.val := by simp [U.eB]
    simp only [liftVec, Sum.elim_inr]
    rw [dif_neg (by rw [h1]; omega)]

theorem mulVec_eB {ρ : ℕ} (M : B.Mat k (j + ρ)) (v : Fin (2 * (j + ρ) + k + 1) → ℂ) (x : Ix k j ρ) :
    (M *ᵥ v) (eB k j ρ x) = ∑ y, M (eB k j ρ x) (eB k j ρ y) * v (eB k j ρ y) := by
  rw [Matrix.mulVec, dotProduct, ← Equiv.sum_comp (eB k j ρ)]

theorem mMap_mulVec_lift (Z : Matrix (Fin j) (Fin j) ℂ) (γ0 : B.Mat k 0) (u : Fin (2 * 0 + k + 1) → ℂ) :
    mMap k j 0 Z γ0 *ᵥ liftVec k j 0 u = liftVec k j 0 (γ0 *ᵥ u) := by
  funext p
  obtain ⟨x, rfl⟩ := (eB k j 0).surjective p
  rw [mulVec_eB, liftVec_eB]
  simp only [mMap, Ux3.block3_apply, liftVec_eB]
  rcases x with (a | i) | a <;>
    simp [Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.fromRows, Matrix.fromCols, Matrix.mulVec, dotProduct]

theorem mMap_inv {ρ : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) (hZ : IsUnit Z.det) (hγ : IsUnit γ.det) :
    (mMap k j ρ Z γ)⁻¹ = mMap k j ρ Zᴴ γ⁻¹ := by
  have hZh : IsUnit Zᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hZ.star
  apply Matrix.inv_eq_right_inv
  rw [U.mMap, U.mMap, Ux5.block3_mul_blocks, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  have e1 : Zᴴ⁻¹ * G.wMat j * (G.wMat j * Zᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (G.wMat j), Ux5.wMat_mul_self, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hZh]
  have e2 : G.wMat j * Z * (Z⁻¹ * G.wMat j) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Z, Matrix.mul_nonsing_inv _ hZ, Matrix.one_mul, Ux5.wMat_mul_self]
  rw [e1, e2, Matrix.mul_nonsing_inv _ hγ, Ux3.block3_one]

theorem liftVec_sub (u v : Fin (2 * 0 + k + 1) → ℂ) : liftVec k j 0 (u - v) = liftVec k j 0 u - liftVec k j 0 v := by
  funext p
  simp only [liftVec, Pi.sub_apply]
  split_ifs <;> simp

theorem liftVec_smul (c : ℂ) (u : Fin (2 * 0 + k + 1) → ℂ) : liftVec k j 0 (c • u) = c • liftVec k j 0 u := by
  funext p
  simp only [liftVec, Pi.smul_apply]
  split_ifs <;> simp

theorem liftVec_eq_jV (u : Fin (2 * 0 + k + 1) → ℂ) : liftVec k j 0 u = TwoByOneBlock.jV k (j + 0) (wbPart k 0 u) := by
  funext p
  simp only [liftVec, TwoByOneBlock.jV, wbPart, wI]
  split_ifs with h1 h2 h2
  · congr 1 <;> ext <;> simp
  · exfalso
    omega
  · exfalso
    omega
  · rfl

theorem herm_lift (u u' : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k (j + 0)) (liftVec k j 0 u) (liftVec k j 0 u') = herm (Hpk k 0) u u' := by
  rw [liftVec_eq_jV, liftVec_eq_jV, TwoByOneBlock.herm_jV]
  have h0 : ∀ v : Fin (2 * 0 + k + 1) → ℂ, TwoByOneBlock.jV k 0 (wbPart k 0 v) = v := fun v =>
    TwoByOneBlock.jV_wbPart (fun i hi => by omega)
  conv_rhs => rw [← h0 u, ← h0 u', TwoByOneBlock.herm_jV]

theorem prW_lift (a u : Fin (2 * 0 + k + 1) → ℂ) :
    D.prW k (j + 0) (liftVec k j 0 a) (liftVec k j 0 u) = liftVec k j 0 (D.prW k 0 a u) := by
  have hb : (fun i : Fin (2 * (j + 0) + k + 1) =>
      if j + 0 ≤ i.val ∧ i.val ≤ j + 0 + k then liftVec k j 0 u i else 0) = liftVec k j 0 u := by
    funext i; split_ifs with h
    · rfl
    · unfold liftVec; rw [dif_neg (by omega)]
  have hb0 : (fun i : Fin (2 * 0 + k + 1) => if 0 ≤ i.val ∧ i.val ≤ 0 + k then u i else 0) = u := by
    funext i; rw [if_pos ⟨Nat.zero_le _, by omega⟩]
  unfold D.prW
  simp only []
  rw [hb, hb0, herm_lift, herm_lift, liftVec_sub, liftVec_smul]

theorem prW_smul {r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    D.prW k r z (c • v) = c • D.prW k r z v := by
  have hvb : (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then (c • v) i else 0) =
      c • (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  simp only [D.prW, hvb]
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, smul_sub, mul_div_assoc, smul_smul]

end lift

section frame

variable {k j : ℕ}

@[reducible] def uniqueFinZeroSucc : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

attribute [local instance] uniqueFinZeroSucc

theorem lowV_liftVec (u : Fin (2 * 0 + k + 1) → ℂ) : lowV k j 0 (liftVec k j 0 u) = u := by
  funext i
  have hi := i.isLt
  simp only [U.lowV, liftVec]
  split_ifs with h
  · congr 1
    ext
    simp
  · exfalso
    apply h
    constructor <;> omega

theorem det_extendOne (Z : Matrix (Fin j) (Fin j) ℂ) (ζ : ℂ) :
    (Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0) (Matrix.fromBlocks Z 0 0 (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ))).det =
      Z.det * ζ := by
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_unique (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ)]
  rfl

theorem adjugate_block_diagonal_single (Z : Matrix (Fin j) (Fin j) ℂ) (ζ : ℂ) (hZ : IsUnit Z.det) (hζ : ζ ≠ 0) :
    (Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0) (Matrix.fromBlocks Z 0 0 (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ))).adjugate =
      Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0)
        (Matrix.fromBlocks (ζ • Z.adjugate) 0 0 (Matrix.of fun (_ _ : Fin (0 + 1)) => Z.det)) := by
  set M := Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0) (Matrix.fromBlocks Z 0 0 (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ))
  set X := Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0)
        (Matrix.fromBlocks (ζ • Z.adjugate) 0 0 (Matrix.of fun (_ _ : Fin (0 + 1)) => Z.det))
  have hM : IsUnit M.det := by
    rw [det_extendOne]; exact (hZ.mul (isUnit_iff_ne_zero.2 hζ))
  have hMX : M * X = M * M.adjugate := by
    rw [Matrix.mul_adjugate, det_extendOne]
    simp only [M, X, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.mul_adjugate]
    ext a b
    obtain ⟨x, rfl⟩ := (Ux3.eC j 0).surjective a
    obtain ⟨y, rfl⟩ := (Ux3.eC j 0).surjective b
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.smul_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq]
    rcases x with x | x <;> rcases y with y | y
    · simp [Matrix.fromBlocks_apply₁₁, Matrix.one_apply, smul_smul, mul_comm]
    · simp
    · simp
    · have : x = y := Fin.ext (by have := x.isLt; have := y.isLt; omega)
      subst this
      simp [Matrix.mul_apply, mul_comm]
  calc M.adjugate = M⁻¹ * (M * M.adjugate) := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hM]
    _ = M⁻¹ * (M * X) := by rw [hMX]
    _ = X := Matrix.nonsing_inv_mul_cancel_left _ _ hM

theorem eC_last : Ux3.eC j 0 (Sum.inr 0) = Fin.last (j + 0) := by
  ext
  simp [Ux3.eC]

theorem adjugate_block_single_last_column (Z : Matrix (Fin j) (Fin j) ℂ) (ζ : ℂ) (hZ : IsUnit Z.det) (hζ : ζ ≠ 0) (b : Fin (j + 0 + 1)) :
    (Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0) (Matrix.fromBlocks Z 0 0 (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ))).adjugate
      b (Fin.last (j + 0)) = if b = Fin.last (j + 0) then Z.det else 0 := by
  rw [adjugate_block_diagonal_single Z ζ hZ hζ, ← eC_last]
  obtain ⟨x, rfl⟩ := (Ux3.eC j 0).surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases x with x | x
  · simp
  · have : x = 0 := Fin.ext (by have := x.isLt; simp)
    subst this; simp

theorem adjugate_block_single_last_line (Z : Matrix (Fin j) (Fin j) ℂ) (ζ : ℂ) (hZ : IsUnit Z.det) (hζ : ζ ≠ 0) (a : Fin (j + 0 + 1)) :
    (Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0) (Matrix.fromBlocks Z 0 0 (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ))).adjugate
      (Fin.last (j + 0)) a = if a = Fin.last (j + 0) then Z.det else 0 := by
  rw [adjugate_block_diagonal_single Z ζ hZ hζ, ← eC_last]
  obtain ⟨x, rfl⟩ := (Ux3.eC j 0).surjective a
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases x with x | x
  · simp
  · have : x = 0 := Fin.ext (by have := x.isLt; simp)
    subst this; simp

theorem herm_eB (u v : Fin (2 * (j + 0) + k + 1) → ℂ) :
    herm (Hpk k (j + 0)) u v = ∑ x : Ix k j 0, star (v (eB k j 0 x)) * (Hpk k (j + 0) *ᵥ u) (eB k j 0 x) := by
  rw [herm, dotProduct, ← Equiv.sum_comp (eB k j 0)]
  rfl

theorem hpk_mulVec_e (u : Fin (2 * (j + 0) + k + 1) → ℂ) (a : Fin j) :
    (Hpk k (j + 0) *ᵥ u) (eB k j 0 (Sum.inl (Sum.inl a))) = u (eB k j 0 (Sum.inr a.rev)) := by
  rw [Ux3.hpkBlocks k j 0, mulVec_eB]
  simp only [Ux3.block3_apply]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
    Matrix.fromCols_apply_inr, G.wMat]

theorem hpk_mulVec_es (u : Fin (2 * (j + 0) + k + 1) → ℂ) (a : Fin j) :
    (Hpk k (j + 0) *ᵥ u) (eB k j 0 (Sum.inr a)) = u (eB k j 0 (Sum.inl (Sum.inl a.rev))) := by
  rw [Ux3.hpkBlocks k j 0, mulVec_eB]
  simp only [Ux3.block3_apply]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.fromRows, Matrix.fromCols, G.wMat]

theorem mMap_col (Z : Matrix (Fin j) (Fin j) ℂ) (γ0 : B.Mat k 0) (b : Fin j) (x : Ix k j 0) :
    (mMap k j 0 Z γ0 *ᵥ bvec (eB k j 0 (Sum.inl (Sum.inl b)))) (eB k j 0 x) =
      Sum.elim (fun _ => 0) (fun a => (G.wMat j * Z) a b) x := by
  rw [mulVec_eB]
  have hb : ∀ y : Ix k j 0, bvec (eB k j 0 (Sum.inl (Sum.inl b))) (eB k j 0 y) =
      if y = Sum.inl (Sum.inl b) then 1 else 0 := by
    intro y; simp only [bvec, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
  simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mMap, Ux3.block3_apply]
  rcases x with (a | i) | a <;> simp [Matrix.fromBlocks, Matrix.fromRows, Matrix.fromCols]

theorem eI_eB (a : Fin j) : eI k (j + 0) ⟨a.val, by omega⟩ = eB k j 0 (Sum.inl (Sum.inl a)) := by
  ext
  simp [eI, U.eB]

theorem orth_lift (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det) (γ0 : B.Mat k 0)
    (u : Fin (2 * (j + 0) + k + 1) → ℂ)
    (h1 : ∀ a : Fin j, herm (Hpk k (j + 0)) u (bvec (eB k j 0 (Sum.inl (Sum.inl a)))) = 0)
    (h2 : ∀ b : Fin j, herm (Hpk k (j + 0)) u (mMap k j 0 Z γ0 *ᵥ bvec (eB k j 0 (Sum.inl (Sum.inl b)))) = 0) :
    u = liftVec k j 0 (lowV k j 0 u) := by
  have hs : ∀ c : Fin j, u (eB k j 0 (Sum.inr c)) = 0 := by
    intro c
    have h := h1 c.rev
    unfold herm at h
    simp only [dotProduct, Pi.star_apply, bvec] at h
    rw [Finset.sum_eq_single (eB k j 0 (Sum.inl (Sum.inl c.rev)))] at h
    · rw [Pi.single_eq_same, star_one, one_mul, hpk_mulVec_e, Fin.rev_rev] at h; exact h
    · intro p _ hp; rw [Pi.single_eq_of_ne hp, star_zero, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have he : ∀ c : Fin j, u (eB k j 0 (Sum.inl (Sum.inl c))) = 0 := by
    set xe : Fin j → ℂ := fun c => u (eB k j 0 (Sum.inl (Sum.inl c)))
    have hZH : Zᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact (hZ.star).ne_zero
    have h0 : Zᴴ *ᵥ xe = 0 := by
      funext b
      have h := h2 b
      rw [herm_eB] at h
      simp only [Fintype.sum_sum_type, mMap_col, Sum.elim_inl, Sum.elim_inr, star_zero, zero_mul,
        Finset.sum_const_zero, zero_add, hpk_mulVec_es] at h
      rw [Pi.zero_apply, ← h]
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, xe]
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [G.wMat, Matrix.mul_apply, Fin.revPerm]
    have := Matrix.eq_zero_of_mulVec_eq_zero hZH h0
    intro c; exact congrFun this c
  funext p
  obtain ⟨x, rfl⟩ := (eB k j 0).surjective p
  rw [liftVec_eB]
  rcases x with (c | i) | c
  · exact he c
  · simp only [Sum.elim_inl, Sum.elim_inr, lowV]
    congr 1
  · exact hs c

theorem fvec_last {r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem fvec_low {r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (ha : a.val < r) :
    fvec k r z a = bvec (eI k r ⟨a.val, ha⟩) := by
  rw [fvec, dif_pos ha]

theorem adj_one (ζ : ℂ) (a b : Fin (0 + 1)) : (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ).adjugate a b = 1 := by
  have hab : a = b := Subsingleton.elim a b
  subst hab
  rw [show (Matrix.of fun (_ _ : Fin (0 + 1)) => ζ).adjugate = 1 from Matrix.adjugate_fin_one _]
  exact Matrix.one_apply_eq a

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem dFrame_mMap (S : B.RealPlaceData k (j + 0) Wp Wq) (S0 : B.RealPlaceData k 0 Wp Wq)
    (hz : S.z = liftVec k j 0 S0.z) (hz' : S.z' = liftVec k j 0 S0.z')
    (ν0 : Fin (2 * 0 + k + 1) → ℂ) (m0 : B.Mat k 0) (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det)
    (γ0 : B.Mat k 0) (hγ0 : IsUnit γ0.det) (ζ : ℂ) (hζ : ζ ≠ 0)
    (hZ0 : Zhat k 0 S0.z S0.z' γ0 = Matrix.of fun _ _ => ζ) (hD : D.IsDFrame S0 ν0 m0 γ0) :
    D.IsDFrame S (liftVec k j 0 ν0) (ιLev k j 0 m0) (mMap k j 0 Z γ0) := by
  have hZh : Zhat k (j + 0) S.z S.z' (mMap k j 0 Z γ0) =
      Matrix.reindex (Ux3.eC j 0) (Ux3.eC j 0) (Matrix.fromBlocks Z 0 0 (Matrix.of fun _ _ => ζ)) := by
    rw [zhat_mMap S.z S.z' S.z_mem S.z'_mem, hz, hz', lowV_liftVec, lowV_liftVec, hZ0]
  have hdet : (Zhat k (j + 0) S.z S.z' (mMap k j 0 Z γ0)).det = Z.det * ζ := by rw [hZh, det_extendOne]
  have hdet0 : (Zhat k 0 S0.z S0.z' γ0).det = ζ := by rw [hZ0, Matrix.det_unique]; rfl
  have hinv : (mMap k j 0 Z γ0)⁻¹ = mMap k j 0 Zᴴ γ0⁻¹ := mMap_inv Z γ0 hZ hγ0
  have hcofR : D.cofR S (mMap k j 0 Z γ0) = Z.det • (mMap k j 0 Z γ0 *ᵥ S.z') := by
    unfold D.cofR
    rw [hZh, Finset.sum_eq_single (Fin.last (j + 0))]
    · rw [adjugate_block_single_last_column Z ζ hZ hζ, if_pos rfl, fvec_last]
    · intro b _ hb; rw [adjugate_block_single_last_column Z ζ hZ hζ, if_neg hb, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcofL : D.cofL S (mMap k j 0 Z γ0) = star Z.det • S.z := by
    unfold D.cofL
    rw [hZh, Finset.sum_eq_single (Fin.last (j + 0))]
    · rw [adjugate_block_single_last_line Z ζ hZ hζ, if_pos rfl, fvec_last]; rfl
    · intro b _ hb; rw [adjugate_block_single_last_line Z ζ hZ hζ, if_neg hb]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcofR0 : D.cofR S0 γ0 = γ0 *ᵥ S0.z' := by
    unfold D.cofR
    rw [Fintype.sum_eq_single (Fin.last 0) (fun b hb => absurd (Fin.ext (by have := b.isLt; simp)) hb),
      hZ0, adj_one, one_smul, fvec_last]
  have hcofL0 : D.cofL S0 γ0 = S0.z := by
    unfold D.cofL
    rw [Fintype.sum_eq_single (Fin.last 0) (fun b hb => absurd (Fin.ext (by have := b.isLt; simp)) hb),
      hZ0, adj_one, fvec_last]
    simp
  obtain ⟨⟨a0, ha0, h1⟩, ⟨b0, hb0, h2⟩, h3⟩ := hD
  refine ⟨⟨a0, ha0, ?_⟩, ⟨b0, hb0, ?_⟩, ?_⟩
  · rw [hdet, hcofR, hz', mMap_mulVec_lift, hz, prW_smul, prW_lift, ← hcofR0, h1, hdet0, liftVec_smul,
      Dx2.Tower.lev_mulVec_lift, smul_smul]
    congr 1; ring
  · rw [hdet, hcofL, hinv, Matrix.mulVec_smul, hz, mMap_mulVec_lift, hz', prW_smul, prW_lift, ← hcofL0, h2, hdet0,
      liftVec_smul, smul_smul, map_mul]
    congr 1; simp only [Complex.star_def]; ring
  · intro u hu
    have hu1 : ∀ a : Fin j, herm (Hpk k (j + 0)) u (bvec (eB k j 0 (Sum.inl (Sum.inl a)))) = 0 := by
      intro a
      have := (hu ⟨a.val, by omega⟩).1
      rwa [fvec_low _ _ (by simp), eI_eB] at this
    have hu2 : ∀ b : Fin j,
        herm (Hpk k (j + 0)) u (mMap k j 0 Z γ0 *ᵥ bvec (eB k j 0 (Sum.inl (Sum.inl b)))) = 0 := by
      intro b
      have := (hu ⟨b.val, by omega⟩).2
      rwa [fvec_low _ _ (by simp), eI_eB] at this
    have hlift := orth_lift Z hZ γ0 u hu1 hu2
    set u0 := lowV k j 0 u
    have hz0 : herm (Hpk k 0) u0 S0.z = 0 := by
      have := (hu (Fin.last (j + 0))).1
      rwa [fvec_last, hlift, hz, herm_lift] at this
    have hz0' : herm (Hpk k 0) u0 (γ0 *ᵥ S0.z') = 0 := by
      have := (hu (Fin.last (j + 0))).2
      rwa [fvec_last, hlift, hz', mMap_mulVec_lift, herm_lift] at this
    have h3u := h3 u0 (fun a => by
      have ha : a = Fin.last 0 := Fin.ext (by have := a.isLt; simp)
      subst ha; rw [fvec_last, fvec_last]; exact ⟨hz0, hz0'⟩)
    rw [hlift, hinv, mMap_mulVec_lift, hz, hz', prW_lift, prW_lift, h3u, Dx2.Tower.lev_mulVec_lift]

end frame

end Formalism.FourierDecayAlt.P.PBM
