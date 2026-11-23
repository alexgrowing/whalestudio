import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.FrameOnto

theorem exists_congr_one {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosDef) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ Sᴴ * M * S = 1 := by
  classical
  set U : Matrix n n ℂ := (hM.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) := by
    have h := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    exact h
  set c : n → ℂ := fun i => (RCLike.ofReal ((Real.sqrt (hM.1.eigenvalues i))⁻¹) : ℂ) with hc
  refine ⟨U * diagonal c, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine IsUnit.mul (isUnit_det_of_left_inverse (Unitary.coe_star_mul_self _)) ?_
    refine Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    exact RCLike.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr (hM.eigenvalues_pos i)))
  · have hs : (U * diagonal c)ᴴ * M * (U * diagonal c) = diagonal (star c) * (star U * M * U) * diagonal c := by
      rw [conjTranspose_mul, diagonal_conjTranspose, ← star_eq_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [hs, hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hl := hM.eigenvalues_pos i
    have hr : (Real.sqrt (hM.1.eigenvalues i))⁻¹ * hM.1.eigenvalues i * (Real.sqrt (hM.1.eigenvalues i))⁻¹ = 1 := by
      have h0 : Real.sqrt (hM.1.eigenvalues i) ≠ 0 := Real.sqrt_ne_zero'.mpr hl
      have h2 := Real.mul_self_sqrt hl.le
      field_simp
      linarith
    simp only [hc, Pi.star_apply, Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, hr, RCLike.ofReal_one]

private lemma posDef_one_sub_mul_conjTranspose_of_posDef {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := by
  have hsd : (1 - z * zᴴ).PosSemidef := by
    haveI : Invertible (1 : Matrix (Fin p) (Fin p) ℂ) := invertibleOne
    haveI : Invertible (1 : Matrix (Fin q) (Fin q) ℂ) := invertibleOne
    have h1 : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) z zᴴ 1).PosSemidef := by
      rw [PosDef.fromBlocks₁₁ (A := (1 : Matrix (Fin p) (Fin p) ℂ)) z 1 PosDef.one]
      simpa using hz.posSemidef
    rw [PosDef.fromBlocks₂₂ 1 z (D := (1 : Matrix (Fin q) (Fin q) ℂ)) PosDef.one] at h1
    simpa using h1
  rw [hsd.posDef_iff_det_ne_zero]
  have hu : IsUnit (1 - zᴴ * z).det := (isUnit_iff_isUnit_det _).mp hz.isUnit
  refine (isUnit_det_of_right_inverse (B := 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ) ?_).ne_zero
  have h := mul_nonsing_inv _ hu
  calc (1 - z * zᴴ) * (1 + z * (1 - zᴴ * z)⁻¹ * zᴴ)
      = 1 - z * zᴴ + z * ((1 - zᴴ * z) * (1 - zᴴ * z)⁻¹) * zᴴ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
          Matrix.one_mul, Matrix.mul_assoc]
    _ = 1 := by
        rw [h, Matrix.mul_one]
        abel

theorem exists_moeb_zero {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    ∃ g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, gᴴ * Jpq p q * g = Jpq p q ∧ moeb g 0 = z := by
  classical
  have hQ : (1 - zᴴ * z).PosDef := hz
  obtain ⟨S, hSu, hS⟩ := exists_congr_one hQ
  obtain ⟨T, hTu, hT⟩ := exists_congr_one (posDef_one_sub_mul_conjTranspose_of_posDef hQ)
  have hJ : Jpq p q = fromBlocks 1 0 0 (-1) := rfl
  refine ⟨fromBlocks T (z * S) (zᴴ * T) S, ?_, ?_⟩
  · rw [hJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · refine Eq.trans ?_ hT
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · refine Eq.trans ?_ (congrArg Neg.neg hS)
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
  · unfold moeb
    rw [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
      Matrix.mul_zero, Matrix.mul_zero, zero_add, zero_add, Matrix.mul_assoc, mul_nonsing_inv _ hSu,
      Matrix.mul_one]

private lemma gram_eq_upper_bounds {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma coe_idx_symm_inl {r j : ℕ} (hj : j ≤ r) (a : Fin j) :
    (((idx hj).symm (Sum.inl a) : Fin r) : ℕ) = r - j + a := by
  unfold idx
  simp

private lemma coe_idx_symm_inr {r j : ℕ} (hj : j ≤ r) (b : Fin (r - j)) :
    (((idx hj).symm (Sum.inr b) : Fin r) : ℕ) = b := by
  unfold idx
  simp

private lemma reindex_diagonal_sgn_eq_neg_Jpq {r j : ℕ} (hj : j ≤ r) :
    reindex (idx hj) (idx hj) (diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (r - j) a : ℝ) : ℂ)) =
      -Jpq j (r - j) := by
  have hJ : Jpq j (r - j) = fromBlocks 1 0 0 (-1) := rfl
  rw [hJ]
  ext (a | a) (b | b) <;>
    simp [reindex_apply, diagonal_apply, coe_idx_symm_inl, coe_idx_symm_inr, ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.one_apply] <;>
    split_ifs <;> simp

theorem frame_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z ∈ DomI Tau j (r - j), ∃ x ∈ X.dom, domPt X hj κ x = z := by
  intro E _ _ _ r j X hj Tau _ κ hp z hz
  classical
  have hz' : ∀ t, z t ∈ hcDom j (r - j) := hz
  choose g hg hgz using fun t => exists_moeb_zero (hz' t)
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) with hD
  have hDJ : reindex (idx hj) (idx hj) D = -Jpq j (r - j) := by
    rw [hD, hp]
    exact reindex_diagonal_sgn_eq_neg_Jpq hj
  have hD' : D = reindex (idx hj).symm (idx hj).symm (-Jpq j (r - j)) := by
    rw [← hDJ]
    simp [reindex_apply, Matrix.submatrix_submatrix]
  have hDT : Dᵀ = D := by
    rw [hD]
    exact diagonal_transpose _
  have hx0 : ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ) = D := fun τ => (X.signature τ).choose_spec
  have hgy : ∀ t, (reindex (idx hj).symm (idx hj).symm (g t))ᴴ * D * reindex (idx hj).symm (idx hj).symm (g t) = D := by
    intro t
    rw [hD']
    simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [Matrix.mul_neg, Matrix.neg_mul, hg t]
  have hT : ∀ y : Matrix (Fin r) (Fin r) ℂ,
      yᵀ * D * y.map (starRingEnd ℂ) = (yᴴ * Dᵀ * y)ᵀ := by
    intro y
    have h1 : (yᴴ)ᵀ = y.map (starRingEnd ℂ) := by
      ext a b
      simp
    rw [transpose_mul, transpose_mul, transpose_transpose, h1, Matrix.mul_assoc]
  let x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := fun τ =>
    (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) :=
    fun τ => rfl
  have hgram : ∀ τ : X.Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = D := by
    intro τ
    have h0 := (hx0 τ).2
    rw [hm, gram_eq_upper_bounds]
    rw [gram_eq_upper_bounds] at h0
    have hre : (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * X.Gm.map τ.1 *
        (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) =
        (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * ((ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ)ᵀ * X.Gm.map τ.1 *
          (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).map (starRingEnd ℂ)) *
          (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) := by
      rw [transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [hre, h0, hT, hDT, hgy, hDT]
  refine ⟨x, ?_, ?_⟩
  · show ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re
    intro τ
    have hsg : ∀ a : ℕ, ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := by
      intro a
      unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
      split_ifs <;> norm_num
    refine ⟨?_, ?_⟩
    · intro hdet
      have h := congrArg Matrix.det (hgram τ)
      rw [gram_eq_upper_bounds, det_mul, det_mul, det_transpose, hdet, zero_mul, zero_mul, hD,
        det_diagonal] at h
      exact (Finset.prod_ne_zero_iff.mpr fun (a : Fin r) _ => Complex.ofReal_ne_zero.mpr (hsg a)) h.symm
    · intro i
      have hl : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.psgn
        rw [hgram τ, hD, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
        simp only [Function.comp_apply, Fin.coe_castLE]
        rw [Fin.prod_univ_eq_prod_range (fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ),
          Complex.ofReal_prod]
      have hps : ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.psgn
        exact Finset.prod_ne_zero_iff.mpr fun a _ => hsg a
      rw [hl, Complex.ofReal_re]
      exact mul_self_pos.mpr hps
  · funext t
    have hf : frameCo X hj x (κ t) = g t := by
      unfold frameCo
      rw [hm, ← Matrix.mul_assoc, nonsing_inv_mul _ (hx0 (κ t)).1.isUnit, Matrix.one_mul,
        Equiv.symm_apply_apply]
      simp [reindex_apply, Matrix.submatrix_submatrix]
    show moeb (frameCo X hj x (κ t)) 0 = z t
    rw [hf, hgz t]

end GlobalTheory.TrueCx.FrameOnto
