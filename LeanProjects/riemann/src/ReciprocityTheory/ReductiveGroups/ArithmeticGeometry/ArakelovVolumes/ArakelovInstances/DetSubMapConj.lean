import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Dsg : Fin r → ℝ := fun a => sgn X.p0 (a : ℕ)

theorem Dsg_ne (a : Fin r) : Dsg X a ≠ 0 := by
  unfold Dsg sgn
  split_ifs <;> norm_num

def Xd (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat (nmat X z) τ)⁻¹ * KapPf.Lin X τ u

def Yd (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat b τ)⁻¹ * Xd X z u τ * mat b τ

theorem nmat_det_unit (z : V (nd X)) (τ : X.Ψ) : IsUnit (mat (nmat X z) τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (KapPf.isUnit_nmat X τ z)

theorem mat_line (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (ζ : ℂ) :
    mat (cpt X x0 (z + ζ • u)) τ =
      mat (rmul (cpt X x0 z) b) τ * ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹) := by
  have hBu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
  have hNu := nmat_det_unit X z τ
  show mat x0 τ * mat (nmat X (z + ζ • u)) τ =
    mat x0 τ * mat (nmat X z) τ * mat b τ *
      ((1 + ζ • ((mat b τ)⁻¹ * ((mat (nmat X z) τ)⁻¹ * KapPf.Lin X τ u) * mat b τ)) * (mat b τ)⁻¹)
  rw [KapPf.nmat_eq X (z + ζ • u) τ, map_add, map_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hBu, Matrix.mul_nonsing_inv _ hBu,
    Matrix.mul_nonsing_inv_cancel_left _ _ hNu]
  rw [KapPf.nmat_eq X z τ]
  simp only [Matrix.mul_add, Matrix.mul_one]
  abel

theorem upper_inv (B : Matrix (Fin r) (Fin r) ℂ) (hBd : B.det ≠ 0) (hB : ∀ a c : Fin r, c < a → B a c = 0) :
    ∀ a c : Fin r, c < a → B⁻¹ a c = 0 := by
  intro a c hca
  have := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hBd)
  have hBT : B.BlockTriangular id := fun i j h => hB i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular hBT) hca

theorem det_sub_map_conj (M : Matrix (Fin r) (Fin r) ℂ) {m : ℕ} (hm : m ≤ r) :
    ((M.map (starRingEnd ℂ)).submatrix (Fin.castLE hm) (Fin.castLE hm)).det =
      starRingEnd ℂ (M.submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  rw [Matrix.submatrix_map]
  exact (RingHom.map_det _ _).symm

theorem dmin_line (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ)
    (hgram : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (ζ : ℂ) (k : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 (z + ζ • u)) τ k =
      ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        starRingEnd ℂ (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) ζ).det *
        starRingEnd ℂ ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
          (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  have hk := Nat.le_of_lt_succ k.isLt
  have hL : ∀ a c : Fin r, c < a → (mat b τ)⁻¹ a c = 0 :=
    upper_inv (mat b τ) (hb τ).1 (fun a c h => (hb τ).2 a c h)
  have hU : ∀ a c : Fin r, c < a → ((mat b τ)⁻¹.map (starRingEnd ℂ)) a c = 0 := by
    intro a c h
    rw [Matrix.map_apply, hL a c h, map_zero]
  have hgram' : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ) := hgram
  have hre : ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹).map (starRingEnd ℂ) =
      ((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ) := by
    rw [Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  calc dmin X.Gm (cpt X x0 (z + ζ • u)) τ k
      = lminor (((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
          (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ)) k := by
        show lminor (gram τ.1 X.Gm (mat (cpt X x0 (z + ζ • u)) τ)) k = _
        rw [mat_line X x0 b hb z u τ ζ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, hgram', hre]
    _ = ((mat b τ)⁻¹.submatrix (Fin.castLE hk) (Fin.castLE hk)).det *
          lminor ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
            (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) k *
          (((mat b τ)⁻¹.map (starRingEnd ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det :=
        lminor_LMU _ _ _ hL hU k
    _ = _ := by
        rw [tr_D_conj, lminor_map_conj, det_sub_map_conj (mat b τ)⁻¹ hk]
        rfl

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
