import Mathlib

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux

set_option linter.unusedSectionVars false

variable {n : Type} [Fintype n] [DecidableEq n]

theorem herm_swap (A : Matrix n n ℂ) (hA : A.IsHermitian) (a b : n → ℂ) :
    star b ⬝ᵥ (A *ᵥ a) = star (star a ⬝ᵥ (A *ᵥ b)) := by
  rw [Matrix.star_dotProduct a (A *ᵥ b), star_star, Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]

theorem herm_re_swap (A : Matrix n n ℂ) (hA : A.IsHermitian) (a b : n → ℂ) :
    (star b ⬝ᵥ (A *ᵥ a)).re = (star a ⬝ᵥ (A *ᵥ b)).re := by
  rw [herm_swap A hA a b]
  simp

theorem herm_im (A : Matrix n n ℂ) (hA : A.IsHermitian) (a : n → ℂ) :
    (star a ⬝ᵥ (A *ᵥ a)).im = 0 := by
  have h := congrArg Complex.im (herm_swap A hA a a)
  simp at h
  linarith

theorem expand (A : Matrix n n ℂ) (u v : n → ℂ) (s : ℂ) :
    star (u + s • v) ⬝ᵥ (A *ᵥ (u + s • v)) = star u ⬝ᵥ (A *ᵥ u) + s * (star u ⬝ᵥ (A *ᵥ v)) +
      star s * (star v ⬝ᵥ (A *ᵥ u)) + star s * s * (star v ⬝ᵥ (A *ᵥ v)) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem re_nonneg_psd {H : Matrix n n ℂ} (hH : H.PosSemidef) (x : n → ℂ) :
    0 ≤ (star x ⬝ᵥ (H *ᵥ x)).re := by
  have := hH.dotProduct_mulVec_nonneg x
  exact (Complex.nonneg_iff.1 this).1

private theorem hermitian_form_add_real_smul_expand (M : Matrix n n ℂ) (hM : M.IsHermitian) (u v : n → ℂ) (s : ℝ) :
    (star (u + (s:ℂ) • v) ⬝ᵥ (M *ᵥ (u + (s:ℂ) • v))).re =
      (star u ⬝ᵥ (M *ᵥ u)).re + 2 * s * (star u ⬝ᵥ (M *ᵥ v)).re + s ^ 2 * (star v ⬝ᵥ (M *ᵥ v)).re := by
  have hs : star (s:ℂ) = s := by simp
  rw [expand, hs, ← Complex.ofReal_mul]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  rw [herm_re_swap M hM u v]
  ring

private theorem re_inner_sq_le_sq_mul_of_hermitian_form_bound (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) (δ : ℝ)
    (hb : ∀ x : n → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (H *ᵥ x)).re) (u v : n → ℂ) :
    ((star u ⬝ᵥ (A *ᵥ v)).re) ^ 2 ≤ δ ^ 2 * (star u ⬝ᵥ (H *ᵥ u)).re * (star v ⬝ᵥ (H *ᵥ v)).re := by
  have hq : ∀ t : ℝ, 0 ≤ (δ * (star v ⬝ᵥ (H *ᵥ v)).re) * (t * t) + (-2 * (star u ⬝ᵥ (A *ᵥ v)).re) * t
      + δ * (star u ⬝ᵥ (H *ᵥ u)).re := by
    intro t
    have b1 := hb (u + (t:ℂ) • v)
    have b2 := hb (u + ((-t:ℝ):ℂ) • v)
    rw [hermitian_form_add_real_smul_expand A hA, hermitian_form_add_real_smul_expand H hH] at b1
    rw [hermitian_form_add_real_smul_expand A hA, hermitian_form_add_real_smul_expand H hH] at b2
    have c1 := (abs_le.mp b1).2
    have c2 := (abs_le.mp b2).1
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem csq (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.PosSemidef) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ x : n → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (H *ᵥ x)).re) (u v : n → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ v)‖ ^ 2 ≤ δ ^ 2 * (star u ⬝ᵥ (H *ᵥ u)).re * (star v ⬝ᵥ (H *ᵥ v)).re := by
  have hH' := hH.isHermitian
  set c := star u ⬝ᵥ (A *ᵥ v) with hc
  have hu := re_nonneg_psd hH u
  have hv := re_nonneg_psd hH v
  have h := re_inner_sq_le_sq_mul_of_hermitian_form_bound A H hA hH' δ hb u (star c • v)
  have e1 : star u ⬝ᵥ (A *ᵥ (star c • v)) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  have e2 : star (star c • v) ⬝ᵥ (H *ᵥ (star c • v)) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ (H *ᵥ v)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, star_star, smul_eq_mul, smul_eq_mul,
      Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rw [Complex.star_def]
    ring
  rw [e1, e2, Complex.ofReal_re, Complex.re_ofReal_mul] at h
  have hn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hu) hv
  · exact le_of_mul_le_mul_left (by nlinarith [h]) hpos

theorem invmono (A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosDef) (c : ℝ) (hc : 0 < c)
    (hle : ∀ x : n → ℂ, c * (star x ⬝ᵥ (A *ᵥ x)).re ≤ (star x ⬝ᵥ (B *ᵥ x)).re) (u : n → ℂ) :
    c * (star u ⬝ᵥ (B⁻¹ *ᵥ u)).re ≤ (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re := by
  have hAh := hA.isHermitian
  have hBu := hB.isUnit
  have hAu := hA.isUnit
  set y := B⁻¹ *ᵥ u with hy
  set z := A⁻¹ *ᵥ u with hz
  have hBy : B *ᵥ y = u := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det B).mp hBu),
      Matrix.one_mulVec]
  have hAz : A *ᵥ z = u := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hAu),
      Matrix.one_mulVec]
  have e1 : (star u ⬝ᵥ y).re = (star y ⬝ᵥ (B *ᵥ y)).re := by
    rw [hBy, star_dotProduct u y]
    simp
  have e2 : (star z ⬝ᵥ (A *ᵥ z)).re = (star u ⬝ᵥ z).re := by
    rw [hAz, star_dotProduct z u]
    simp
  have e3 : (star y ⬝ᵥ (A *ᵥ z)).re = (star y ⬝ᵥ (B *ᵥ y)).re := by
    rw [hAz, hBy]
  have e4 : (star z ⬝ᵥ (A *ᵥ y)).re = (star y ⬝ᵥ (A *ᵥ z)).re := herm_re_swap A hAh y z
  have hn := re_nonneg_psd hA.posSemidef (z + ((-c:ℝ):ℂ) • y)
  rw [hermitian_form_add_real_smul_expand A hAh z y (-c), e2, e4, e3] at hn
  have hl := hle y
  rw [e1]
  nlinarith [mul_le_mul_of_nonneg_left hl hc.le]

theorem cd_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : Type} [Fintype n] [DecidableEq n]
    {k : WithTop ℕ∞} (f : E → Matrix n n ℂ) (hf : ∀ i j, ContDiff ℝ k (fun x => f x i j)) :
    ContDiff ℝ k (fun x => (f x).det) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod fun i _ => hf _ _)

theorem cd_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : Type} [Fintype n] [DecidableEq n]
    {k : WithTop ℕ∞} (f : E → Matrix n n ℂ) (hf : ∀ i j, ContDiff ℝ k (fun x => f x i j)) (i j : n) (x : E)
    (hx : (f x).det ≠ 0) : ContDiffAt ℝ k (fun x => (f x)⁻¹ i j) x := by
  have hdet : ContDiff ℝ k (fun x => (f x).det) := cd_det f hf
  have hadj : ContDiff ℝ k (fun x => (f x).adjugate i j) := by
    simp only [Matrix.adjugate_apply]
    apply cd_det (fun x => (f x).updateRow j (Pi.single i 1))
    intro a b
    by_cases h : a = j <;> simp [Matrix.updateRow_apply, h, contDiff_const, hf]
  have hinv : ContDiffAt ℝ k (fun x => ((f x).det)⁻¹) x := hdet.contDiffAt.inv hx
  have heq : (fun x => (f x)⁻¹ i j) = fun x => ((f x).det)⁻¹ * (f x).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact hinv.mul hadj.contDiffAt

end PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux
