import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem uMat_conj_eq_diagonal {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ d : Fin n → ℝ, (∀ k : Fin n, 0 < sgn p0 k * d k) ∧
      (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) = Matrix.diagonal fun a => ((d a : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := hs ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  refine ⟨fun k => (B k k).re, fun k => ?_, ?_⟩
  · have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
      rw [hprod k.succ, hprod k.castSucc]
      exact prod_castLE_succ (f := fun k => B k k) k.isLt
    have h1 := hs k.succ
    have h0 := hs k.castSucc
    rw [hsucc, Complex.mul_re, hre, mul_zero, sub_zero, Fin.val_succ, psgn_succ] at h1
    rw [Fin.val_castSucc] at h0
    refine (pos_iff_pos_of_mul_pos (a := psgn p0 k * (lminor A k.castSucc).re) ?_).1 h0
    exact h1.trans_eq (by ring)
  · rw [hdiag]
    congr 1
    funext k
    apply Complex.ext <;> simp [hre]

theorem exists_upper_conj_eq_signature {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, b.det ≠ 0 ∧ b.BlockTriangular id ∧
      bᵀ * A * b.map (starRingEnd ℂ)
        = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨d, hd, hA'⟩ := uMat_conj_eq_diagonal p0 A hA hs
  refine ⟨uMat A * Matrix.diagonal fun k : Fin n => (((√(sgn p0 k * d k))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, det_uMat, one_mul, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    exact Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hd k)).ne')
  · exact (uMat_upper A).mul (Matrix.blockTriangular_diagonal _)
  · rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.diagonal_transpose,
      Matrix.diagonal_map (map_zero _), ← Matrix.mul_assoc, Matrix.mul_assoc _ (uMat A)ᵀ,
      Matrix.mul_assoc _ ((uMat A)ᵀ * A), hA',
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
    have h1 := Real.mul_self_sqrt (hd k).le
    have h2 := (Real.sqrt_pos.2 (hd k)).ne'
    set s := √(sgn p0 k * d k)
    have h3 : d k = sgn p0 k * (s * s) := by
      rw [h1]
      rcases sgn_sq p0 k with h | h <;> simp [h]
    rw [h3]
    field_simp

theorem frame_mul_triangular_orthonormal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ x₀ = rmul x b) ∧ ∀ (τ : E →+* ℂ) (x₀ x₁ : Matrix (Fin r) (Fin r) ℂ), gram τ Gm x₀ = (Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → gram τ Gm x₁ = gram τ Gm x₀ → ∃ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ ∧ x₁ = u * x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx => ?_, fun τ x₀ x₁ h0 h1 => ?_⟩
  · choose b hb using fun τ : Ψ => exists_upper_conj_eq_signature p0 (gram τ.1 Gm (mat x τ))
      (gram_isHermitian τ.1 hG _) (hx τ).2
    refine ⟨rmul x fun τ => b τ, fun τ => b τ,
      fun τ => ⟨(hb τ).1, fun a c hca => (hb τ).2.1 hca⟩, fun τ => ?_, rfl⟩
    show gram τ.1 Gm (mat x τ * b τ) = _
    rw [FrameDegreeData.gram_mul]
    exact (hb τ).2.2
  · have hdet : IsUnit x₀.det := by
      refine isUnit_iff_ne_zero.2 fun h => ?_
      have h2 := congrArg Matrix.det h0
      rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul,
        zero_mul, Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
      rcases sgn_sq p0 k with h' | h' <;> simp [h']
    refine ⟨x₁ * x₀⁻¹, ?_, (Matrix.nonsing_inv_mul_cancel_right _ _ hdet).symm⟩
    rw [← FrameDegreeData.gram_eq, FrameDegreeData.gram_mul, h1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hdet,
      FrameDegreeData.gram_eq]
    simp

end GlobalTheory.UnitFrames
