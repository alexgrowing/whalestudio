import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDiagonalMap

variable {k j ρ : ℕ}

theorem leviElement_mul_mMap (W Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) (hW : IsUnit W.det) :
    muP k j ρ W * mMap k j ρ Z γ = mMap k j ρ (Wᴴ⁻¹ * Z) γ := by
  unfold mMap muP
  rw [Ux3.block3_mul]
  have h13 : W * (Zᴴ⁻¹ * G.wMat j) = (Wᴴ⁻¹ * Z)ᴴ⁻¹ * G.wMat j := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hW, Matrix.mul_assoc]
  have h31 : G.wMat j * Wᴴ⁻¹ * G.wMat j * (G.wMat j * Z) = G.wMat j * (Wᴴ⁻¹ * Z) := by
    rw [Matrix.mul_assoc, Ux4.w_w_mul, Matrix.mul_assoc]
  congr 1 <;> simp [h13, h31]

theorem leviElement_nset (p : Matrix (Fin j) (Fin j) ℂ) (hp : Formalism.DoubleCosetMeasures.IsUpUni p) : muP k j ρ p ∈ Nset k (j + ρ) := by
  have hdet : p.det ≠ 0 := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hp]; exact one_ne_zero
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k j ρ).2.1 p hdet, ?_, ?_⟩
  · intro a i hai
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, hy⟩ := (eB k j ρ).surjective (eI k (j + ρ) a)
    unfold muP
    rw [← hy, Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    have hv := congrArg Fin.val hy
    have ha := a.isLt
    simp only [eI] at hv
    rw [← hv] at hai
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hv hai
    all_goals first
      | (exfalso; have := x.isLt; have := y.isLt; omega)
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | skip

    simp only [Matrix.fromBlocks_apply₁₁, Sum.inl.injEq]
    rcases eq_or_lt_of_le hai with h | h
    · have : x = y := Fin.ext h.symm
      subst this; simp [hp.2]
    · have hne : x ≠ y := fun e => by subst e; omega
      rw [if_neg hne]
      exact hp.1 (show y < x from h)
  · intro i c hc1 hc2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective c
    unfold muP
    rw [Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc1 hc2 hi <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)

def eW (k : ℕ) : Fin (2 * 0 + k + 1) ≃ Fin (k + 1) := finCongr (by omega)

def muOf (γ : B.Mat k 0) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.reindex (eW k) (eW k) γ

theorem hb_eq (k : ℕ) : Hb k = Matrix.reindex (eW k) (eW k) (Hpk k 0) := by
  ext i j
  simp only [Hb, Hpk, eW, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, finCongr_symm,
    finCongr_apply, Fin.coe_cast, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

theorem muOf_mem (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) : (muOf γ)ᴴ * Hb k * muOf γ = Hb k := by
  have h : γᴴ * Hpk k 0 * γ = Hpk k 0 := hγ
  rw [hb_eq]
  simp only [muOf, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h]

theorem inv_diag {r : ℕ} (v : Fin r → ℂ) (hv : ∀ a, v a ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun a => (v a)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact inv_mul_cancel₀ (hv a)

theorem mMap_diag (r : ℕ) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ : B.Mat k 0) :
    (mMap k r 0 (Matrix.diagonal d) γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      bigCell k r d (muOf γ) := by
  ext i l
  obtain ⟨x, rfl⟩ := (eB k r 0).surjective i
  obtain ⟨y, rfl⟩ := (eB k r 0).surjective l
  unfold mMap
  rw [Matrix.diagonal_conjTranspose, inv_diag (star d) (fun a => by simpa [Pi.star_apply] using hd a), Ux3.block3_apply]
  have v1 := @Ux3.block_index_first_val k r 0
  have v2 := @Ux3.block_index_middle_val k r 0
  have v3 := @Ux3.block_index_last_val k r 0
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [bigCell, v1, v2, v3, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  all_goals
    have hx := x.isLt
    have hy := y.isLt
    simp only [Fin.ext_iff, v1, v2, v3, esI, G.wMat, Matrix.of_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Ring.inverse_eq_inv', Pi.star_apply, Fin.val_rev, Pi.inv_apply, Complex.star_def, mul_one,
      one_mul, mul_zero, zero_mul]
    split_ifs <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; ext; simp only [Fin.val_mk]; omega)
      | (congr 2; ext; simp only [Fin.val_mk]; omega)
      | (intro h; exfalso; omega)
      | (simp; done)
      | (simp only [mul_one]; congr 3; ext; simp only [Fin.val_mk]; omega)
      | (simp only [muOf, eW, Matrix.reindex_apply, Matrix.submatrix_apply]; congr 1 <;> (ext; simp))
      | skip

theorem dmin_lead {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : ℕ) (hl : l ≤ r) : Dmin k r z z' g ⟨l, by omega⟩ = Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl := by
  unfold Dmin Formalism.FourierDecayAlt.S3.lead
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  rw [Ux3.zhat_apply_low]
  · rfl
  · simp; omega
  · simp; omega

theorem cellDecomp : BigCellDecomposition.CellDecomp := by
  intro k r z z' g hg hD
  have hDl : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl ≠ 0 := fun l hl => by
    rw [← dmin_lead z z' g l hl]; exact hD ⟨l, by omega⟩ hl
  have hDj : DjU k r 0 g ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r 0 z z' g
    rw [← h]; exact hD ⟨r, by omega⟩ le_rfl
  obtain ⟨x, x', Z, γ, _hZ, hγ, hgeq⟩ := Ux3.bigCell_exists (k := k) (j := r) (ρ := 0) g hg hDj
  have hZh : Zh k r 0 g = Z := by rw [hgeq]; exact Formalism.FourierDecayAlt.P.hat_z_on_slice k r 0 x x' Z γ
  have hDZ : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead Z l hl ≠ 0 := by rw [← hZh]; exact hDl
  obtain ⟨L, U, d, hL, hU, hLDU, hlead⟩ :=
    Formalism.FourierDecayAlt.P.ldu_decomposition_exists ℂ r Z (fun l hl => (hDZ l hl.le).isUnit)
  have hd : ∀ a, d a ≠ 0 := fun a h0 => by
    have h1 := hlead a.val a.isLt
    rw [h0, zero_mul] at h1
    exact hDZ (a.val + 1) a.isLt h1
  have hLh : Formalism.DoubleCosetMeasures.IsUpUni Lᴴ := by
    refine ⟨fun i j hij => ?_, fun a => ?_⟩
    · rw [Matrix.conjTranspose_apply, hL.1 hij, star_zero]
    · rw [Matrix.conjTranspose_apply, hL.2 a, star_one]
  have hLu : IsUnit L.det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det ℂ hL]; exact isUnit_one
  have hLhu : IsUnit Lᴴ.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hLh]; exact isUnit_one
  have hP : muP k r 0 Lᴴ ∈ Nset k (r + 0) := leviElement_nset _ hLh
  have hPu : IsUnit (muP k r 0 Lᴴ).det := Ux3.gv_det hP.1
  have h1 : muP k r 0 Lᴴ * mMap k r 0 Z γ = mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U := by
    rw [leviElement_mul_mMap _ _ _ hLhu, Ux4.mMap_mul_muP, hLDU, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul]
  have key : mMap k r 0 Z γ = (muP k r 0 Lᴴ)⁻¹ * (mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U) := by
    rw [← h1, Matrix.nonsing_inv_mul_cancel_left _ _ hPu]
  refine ⟨muP k r 0 Lᴴ * Rn k r 0 x, WeylGroupFacts.mem_n_mul hP (Ux3.rn_nset x),
    muP k r 0 U * Rn k r 0 x', WeylGroupFacts.mem_n_mul (leviElement_nset _ hU) (Ux3.rn_nset x'), d, hd, muOf γ, muOf_mem γ hγ, ?_⟩
  rw [hgeq, key, ← mMap_diag r d hd γ, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.BigCellDiagonalMap

namespace Formalism.FourierDecayAlt.P

theorem big_cell_decomposition : BigCellDecomposition.CellDecomp := by
  exact BigCellDiagonalMap.cellDecomp

theorem psiOnto_true : Formalism.FourierDecayAlt.JF.PsiOnto := jf_psiOnto_of_cellDecomp BigCellDiagonalMap.cellDecomp

theorem equiv_det : Formalism.FourierDecayAlt.JF.EquivDet := jf_equivDet_of_cellDecomp BigCellDiagonalMap.cellDecomp

end Formalism.FourierDecayAlt.P
