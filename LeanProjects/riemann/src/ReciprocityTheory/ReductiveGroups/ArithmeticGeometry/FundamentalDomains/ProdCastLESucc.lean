import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UMatUpper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Mat

variable {n : ℕ}

lemma uGu_lower (G : Matrix (Fin n) (Fin n) ℂ) (hdet : ∀ c : Fin n, (blk G c).det ≠ 0) {a c : Fin n}
    (hac : a < c) : ((uMat G)ᵀ * G * (uMat G).map (starRingEnd ℂ)) c a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge a k with h | h
  · rw [Matrix.map_apply, upper_lt (uMat_upper G) h, map_zero, mul_zero]
  · rw [uT_G_zero G c (hdet c) k (lt_of_le_of_lt h hac), zero_mul]

lemma prod_castLE_succ {k : ℕ} (h : k + 1 ≤ n) (f : Fin n → ℂ) :
    ∏ j : Fin (k + 1), f (Fin.castLE h j) = (∏ j : Fin k, f (Fin.castLE (Nat.le_of_succ_le h) j)) * f ⟨k, h⟩ := by
  rw [Fin.prod_univ_castSucc]
  rfl

lemma lminor_diagonal (D : Fin n → ℂ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal D) i = ∏ j : Fin i, D (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [lminor, det_sub_upper _ (Matrix.blockTriangular_diagonal D)]
  simp

end Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def uOf (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := uMat (gram τ.1 X.Gm (mat x τ))

def dOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := gram τ.1 X.Gm (mat x τ * uOf X x τ) k k

lemma blk_det {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin r) :
    (blk (gram τ.1 X.Gm (mat x τ)) c).det ≠ 0 := by
  intro h0
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 c.castSucc
  have h2 : dmin X.Gm x τ c.castSucc = 0 := h0
  rw [h2, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

lemma gram_u_eq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat x τ * uOf X x τ) = Matrix.diagonal (dOf X x τ) := by
  ext c a
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · rcases lt_or_gt_of_ne h with h' | h'
    · have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
      rw [← hH.apply c a, uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h', star_zero]
    · rw [uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h']

lemma dOf_real {x : Frame X.Ψ r} (_hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : (dOf X x τ k).im = 0 := by
  have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
  exact Complex.conj_eq_iff_im.mp (hH.apply k k)

lemma dmin_prod {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ∏ j : Fin i, dOf X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  have h1 := lminor_conj (N := uOf X x τ) (A := gram τ.1 X.Gm (mat x τ)) (uMat_upper _) i
  rw [← gram_mul, gram_u_eq X hx τ, lminor_diagonal] at h1
  simp only [uOf, uMat_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
  exact h1.symm

lemma dmin_succ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm x τ k.succ = dmin X.Gm x τ k.castSucc * dOf X x τ k := by
  rw [dmin_prod X hx τ, dmin_prod X hx τ]
  exact prod_castLE_succ k.isLt (dOf X x τ)

lemma psgn_succ (p0 k : ℕ) : psgn p0 (k + 1) = psgn p0 k * sgn p0 k := by
  rw [psgn, psgn, Finset.prod_range_succ]

lemma sgn_dOf_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    0 < sgn X.p0 k * (dOf X x τ k).re := by
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 k.castSucc
  have h2 := ((X.mem_dom_iff x).1 hx τ).2 k.succ
  rw [dmin_succ X hx τ k, Complex.mul_re, dOf_real X hx τ k, mul_zero, sub_zero] at h2
  rw [Fin.val_succ, psgn_succ] at h2
  rw [Fin.coe_castSucc] at h1
  by_contra hneg
  push_neg at hneg
  nlinarith

def sOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := ((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ)

def bOf (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix _ _ ℂ)

lemma sgn_sq (p0 k : ℕ) : sgn p0 k = 1 ∨ sgn p0 k = -1 := by
  unfold sgn
  split_ifs <;> simp

lemma abs_re_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : 0 < |(dOf X x τ k).re| := by
  have h := sgn_dOf_pos X hx τ k
  refine abs_pos.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

lemma sOf_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : sOf X x τ k ≠ 0 := by
  unfold sOf
  rw [Ne, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero']
  exact not_le.mpr (abs_re_pos X hx τ k)

lemma bOf_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) : bOf X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)).det ≠ 0
    unfold uOf
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_of_upperTriangular (uMat_upper _)]
    simp only [uMat_diag, Finset.prod_const_one, one_mul]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => sOf_ne X hx τ k
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)) a c = 0
    unfold uOf
    rw [Matrix.mul_diagonal, upper_lt (uMat_upper _) hca, zero_mul]

lemma ortho_bOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.IsOrtho (rmul x (bOf X x)) := by
  intro τ
  change gram τ.1 X.Gm (mat x τ * (uOf X x τ * Matrix.diagonal (sOf X x τ))) = _
  rw [← Matrix.mul_assoc, gram_mul, gram_u_eq X hx τ, Matrix.diagonal_transpose,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  have hd : dOf X x τ a = ((dOf X x τ a).re : ℂ) :=
    Complex.ext (by simp) (by simp [dOf_real X hx τ a])
  have hpos := sgn_dOf_pos X hx τ a
  have habs := abs_re_pos X hx τ a
  rw [hd]
  simp only [sOf, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  set d := (dOf X x τ a).re
  have hs : (Real.sqrt |d|)⁻¹ * d * (Real.sqrt |d|)⁻¹ = d / |d| := by
    rw [mul_comm _ d, mul_assoc, ← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_mul_inv]
  rw [hs]
  rcases sgn_sq X.p0 a with h1 | h1 <;> rw [h1] at hpos ⊢
  · rw [abs_of_pos (by linarith), div_self (by linarith)]
  · have hn : d < 0 := by linarith
    rw [abs_of_neg hn, div_neg, div_self hn.ne]

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
