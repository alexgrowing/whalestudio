import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SmulOneConj

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DSiegH

variable {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem cross_form_linear_fractional_eq_conjTranspose_sub (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) = Wᴴ - W := by
  have e : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) =
      Wᴴ * (Aᴴ * C - Cᴴ * A) * W + Wᴴ * (Aᴴ * D - Cᴴ * B) + (Bᴴ * C - Dᴴ * A) * W + (Bᴴ * D - Dᴴ * B) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [e, sub_eq_zero.2 h1, h3, h4, sub_eq_zero.2 h2]
  noncomm_ring

theorem det_ne (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : ∀ v : Fin n → ℂ, v ≠ 0 → star v ⬝ᵥ ((Wᴴ - W) *ᵥ v) ≠ 0) :
    (C * W + D).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have key := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => star v ⬝ᵥ (M *ᵥ v)) (cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_zero, zero_sub, dotProduct_neg] at key
  have e : star v ⬝ᵥ ((C * W + D)ᴴ *ᵥ ((A * W + B) *ᵥ v)) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hQv, star_zero, zero_dotProduct]
  rw [e, neg_zero] at key
  exact hW v hv (by rw [Matrix.sub_mulVec] at *; simpa [dotProduct_sub] using key.symm)

theorem im_formula (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) :
    (A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ =
      ((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹ := by
  set P := A * W + B
  set Q := C * W + D
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hQh : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQQ, conjTranspose_one]
  have hc : Pᴴ * Q - Qᴴ * P = Wᴴ - W := cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W
  have e1 : P * Q⁻¹ = (Q⁻¹)ᴴ * (Qᴴ * P) * Q⁻¹ := by rw [← Matrix.mul_assoc, hQh, Matrix.one_mul]
  have e2 : (P * Q⁻¹)ᴴ = (Q⁻¹)ᴴ * (Pᴴ * Q) * Q⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [e2, e1, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  have : Qᴴ * P - Pᴴ * Q = -(Pᴴ * Q - Qᴴ * P) := by abel
  rw [this, hc]
  abel

theorem siegel_of (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) (a : ℂ)
    (hW : (a • (W - Wᴴ)).PosDef) :
    (a • ((A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ)).PosDef := by
  rw [im_formula h1 h2 h3 h4 W hQ]
  have e : a • (((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹) =
      ((C * W + D)⁻¹)ᴴ * (a • (W - Wᴴ)) * (C * W + D)⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact hW.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hQ)))

theorem posDef_diag_re (w : Fin n → ℂ) (hw : ∀ j, 0 < (w j).re) (a : ℂ)
    (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) (hsa : a * s * 2 = 1) :
    (a • (s • diagonal w - (s • diagonal w)ᴴ)).PosDef := by
  have e : a • (s • diagonal w - (s • diagonal w)ᴴ) = diagonal fun j => ((w j).re : ℂ) := by
    rw [conjTranspose_smul, diagonal_conjTranspose]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hst : star s = -s := by
        rcases hs with rfl | rfl <;> simp [Complex.conj_I]
      simp only [Matrix.smul_apply, Matrix.sub_apply, diagonal_apply_eq, smul_eq_mul, hst, Pi.star_apply]
      have hw' : (w i : ℂ) + star (w i) = 2 * ((w i).re : ℂ) := by
        rw [Complex.star_def, Complex.add_conj]; push_cast; ring
      calc a * (s * w i - -s * star (w i)) = a * s * ((w i : ℂ) + star (w i)) := by ring
        _ = a * s * (2 * ((w i).re : ℂ)) := by rw [hw']
        _ = ((w i).re : ℂ) := by linear_combination ((w i).re : ℂ) * hsa
    · simp [hij]
  rw [e, Matrix.posDef_diagonal_iff]
  intro j
  exact_mod_cast hw j

theorem det_ne_of_posDef (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1)
    (h4 : Bᴴ * C - Dᴴ * A = -1) (W : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (ha : a ≠ 0) (hX : (a • (W - Wᴴ)).PosDef) :
    (C * W + D).det ≠ 0 := by
  refine det_ne h1 h2 h3 h4 W fun v hv => ?_
  have e : Wᴴ - W = (-a⁻¹) • (a • (W - Wᴴ)) := by
    rw [smul_smul, neg_mul, inv_mul_cancel₀ ha, neg_one_smul, neg_sub]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero ha)) (hX.dotProduct_mulVec_pos hv).ne'

end DSiegH

open DRealH DSiegH in
theorem dSieg : DSieg := by
  intro n y X z hz
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG (g := mR y) y.2
  set A := (mR y).toBlocks₁₁ with hA
  set B := (mR y).toBlocks₁₂ with hB
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  set w : Fin n → ℂ := fun j => Complex.exp (2 * z * X j) with hwdef
  set E : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (z * X j) with hE
  set F : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (-(z * X j)) with hF
  have hwre : ∀ j, 0 < (w j).re := by
    intro j
    simp only [hwdef, Complex.exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    all_goals
      have hj := hz j
      have him : (2 * z * (X j : ℂ)).im = 2 * (z.im * X j) := by simp [Complex.mul_im]; ring
      rw [him]
      rw [abs_lt] at hj
      linarith [hj.1, hj.2]
  have hM : mR y * aC X z = fromBlocks (A * E) (B * F) (C * E) (D * F) := by
    have e : mR y = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    rw [e]
    unfold aC
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, hE, hF]
  have hFu : IsUnit F.det := by
    rw [hF, det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => Complex.exp_ne_zero _)
  have hFF : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ hFu
  have hWF : ∀ s : ℂ, E * (s • 1) = (s • diagonal w) * F := by
    intro s
    rw [hE, hF, Matrix.smul_mul, diagonal_mul_diagonal, Matrix.mul_smul, Matrix.mul_one]
    congr 1
    congr 1
    funext j
    rw [hwdef, ← Complex.exp_add]
    congr 1; ring
  have hblk : ∀ s : ℂ, ((mR y * aC X z).toBlocks₂₁ * (s • 1) + (mR y * aC X z).toBlocks₂₂) = (C * (s • diagonal w) + D) * F ∧
      ((mR y * aC X z).toBlocks₁₁ * (s • 1) + (mR y * aC X z).toBlocks₁₂) = (A * (s • diagonal w) + B) * F := by
    intro s
    rw [hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    constructor
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
  have hpt : ∀ s : ℂ, ptZ y X z s = (A * (s • diagonal w) + B) * (C * (s • diagonal w) + D)⁻¹ := by
    intro s
    simp only [ptZ]
    rw [(hblk s).1, (hblk s).2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFF, Matrix.mul_one]
  have hI2 : -(Complex.I / 2) ≠ 0 := by simp [Complex.I_ne_zero]
  have hI2' : Complex.I / 2 ≠ 0 := by simp [Complex.I_ne_zero]
  have hX1 : ((-(Complex.I / 2)) • ((Complex.I • diagonal w) - (Complex.I • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ Complex.I (Or.inl rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hX2 : ((Complex.I / 2) • (((-Complex.I) • diagonal w) - ((-Complex.I) • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ (-Complex.I) (Or.inr rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hQ1 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2 hX1
  have hQ2 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2' hX2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold IsSiegel
    rw [hpt]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ1) _ hX1
  · unfold IsSiegel
    rw [hpt, conjTranspose_conjTranspose]
    have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, (-(Complex.I / 2)) • (Zᴴ - Z) = (Complex.I / 2) • (Z - Zᴴ) := by
      intro Z; rw [← neg_sub, smul_neg, neg_smul, neg_neg]
    rw [e]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ2) _ hX2
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ1 (isUnit_iff_ne_zero.1 hFu)
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ2 (isUnit_iff_ne_zero.1 hFu)

end PositivityTheory.Rg.Sw.Glob
