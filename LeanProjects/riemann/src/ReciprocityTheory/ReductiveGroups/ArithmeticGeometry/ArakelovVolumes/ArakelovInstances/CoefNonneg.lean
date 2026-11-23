import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.TelePoint

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem coef_nonneg (la : Wt X.Ψ r) (hdom : X.IsDominant la) (τ : X.Ψ) (a j : Fin r) (h : (a : ℕ) < j) :
    0 ≤ coef X la τ a j := by
  obtain ⟨h1, h2', h3⟩ := hdom τ
  have haj : a < j := Fin.lt_def.2 h
  unfold coef Dsg sgn
  by_cases hj : (j : ℕ) < X.p0
  · have ha : (a : ℕ) < X.p0 := by omega
    have hz := h1 a j haj.le hj
    have hr : (la τ j : ℝ) ≤ la τ a := by exact_mod_cast hz
    rw [if_pos hj, if_pos ha]
    norm_num
    linarith
  · by_cases ha : (a : ℕ) < X.p0
    · have hz := h3 a j ha (by omega)
      have hr : (la τ a : ℝ) ≤ la τ j := by exact_mod_cast hz
      rw [if_neg hj, if_pos ha]
      norm_num
      linarith
    · have hz := h2' a j (by omega) haj.le
      have hr : (la τ j : ℝ) ≤ la τ a := by exact_mod_cast hz
      rw [if_neg hj, if_neg ha]
      norm_num
      linarith

theorem coef_pos (la : Wt X.Ψ r) (hs : IsStrictDom X la) (τ : X.Ψ) (a j : Fin r) (h : (a : ℕ) < j) :
    0 < coef X la τ a j := by
  obtain ⟨h1, h2', h3⟩ := hs τ
  have haj : a < j := Fin.lt_def.2 h
  unfold coef Dsg sgn
  by_cases hj : (j : ℕ) < X.p0
  · have ha : (a : ℕ) < X.p0 := by omega
    have hz := h1 a j haj hj
    have hr : (la τ j : ℝ) < la τ a := by exact_mod_cast hz
    rw [if_pos hj, if_pos ha]
    norm_num
    linarith
  · by_cases ha : (a : ℕ) < X.p0
    · have hz := h3 a j ha (by omega)
      have hr : (la τ a : ℝ) < la τ j := by exact_mod_cast hz
      rw [if_neg hj, if_pos ha]
      norm_num
      linarith
    · have hz := h2' a j (by omega) haj
      have hr : (la τ j : ℝ) < la τ a := by exact_mod_cast hz
      rw [if_neg hj, if_neg ha]
      norm_num
      linarith

theorem Lin_ne (u : V (nd X)) (hu : u ≠ 0) : ∃ τ, KapPf.Lin X τ u ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hu
  ext i
  rcases he : (Fintype.equivFin (Ent X)).symm i with ⟨τ, ⟨⟨x, c⟩, hxc⟩⟩
  have hi : Fintype.equivFin (Ent X) ⟨τ, ⟨(x, c), hxc⟩⟩ = i := by
    rw [← he]
    exact Equiv.apply_symm_apply _ _
  have h0 := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M x c) (hall τ)
  simp only [KapPf.Lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, KapPf.embF,
    KapPf.vecOf, hxc, dite_true, Matrix.zero_apply] at h0
  rw [hi] at h0
  simpa using h0

theorem Xd_lower (z u : V (nd X)) (τ : X.Ψ) (i j : Fin r) (hij : i ≤ j) : Xd X z u τ i j = 0 := by
  have hL : (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
    intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.1 hab
    simp [mat, nmat, not_lt.2 hab'.le, hab'.ne]
  have : Invertible (mat (nmat X z) τ) :=
    (mat (nmat X z) τ).invertibleOfIsUnitDet (nmat_det_unit X z τ)
  have hLi := Matrix.blockTriangular_inv_of_blockTriangular hL
  unfold Xd
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hLi (OrderDual.toDual_lt_toDual.2 hik), zero_mul]
  · have hkj : ¬ j < k := fun h => hik (lt_of_le_of_lt hij h)
    have hz : KapPf.Lin X τ u k j = 0 := by
      simp [KapPf.Lin, KapPf.embF, hkj]
    rw [hz, mul_zero]

theorem Yd_ne (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (hu : u ≠ 0) :
    ∃ τ, ∃ a j : Fin r, (a : ℕ) < j ∧ Yd X b z u τ j a ≠ 0 := by
  obtain ⟨τ, hτ⟩ := Lin_ne X u hu
  refine ⟨τ, ?_⟩
  by_contra hall
  push Not at hall
  apply hτ
  have hN : IsUnit (mat (nmat X z) τ).det := nmat_det_unit X z τ
  have hB : (mat b τ).BlockTriangular id := fun a c hca => (hb τ).2 a c hca
  have hBd : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
  have : Invertible (mat b τ) := (mat b τ).invertibleOfIsUnitDet hBd
  have hY : (Yd X b z u τ).BlockTriangular id := fun a c hca => hall c a hca
  have hX : Xd X z u τ = mat b τ * Yd X b z u τ * (mat b τ)⁻¹ := by
    unfold Yd
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hBd]
  have hXu : (Xd X z u τ).BlockTriangular id := by
    rw [hX]
    exact (hB.mul hY).mul (Matrix.blockTriangular_inv_of_blockTriangular hB)
  have hXd : Xd X z u τ = 0 := by
    ext i j
    rcases lt_or_ge j i with h | h
    · exact hXu h
    · exact Xd_lower X z u τ i j h
  have hLin : KapPf.Lin X τ u = mat (nmat X z) τ * Xd X z u τ := by
    unfold Xd
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hN]
  rw [hLin, hXd, Matrix.mul_zero]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
