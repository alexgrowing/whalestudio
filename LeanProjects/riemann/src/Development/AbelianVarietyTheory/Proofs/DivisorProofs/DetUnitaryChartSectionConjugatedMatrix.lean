import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem det_secM_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  intro E _ _ _ r X x hx w hw τ
  have hG := FrameDegreeData.ortho_bOf X hw τ
  rw [bOf_cpt X hx w] at hG
  have hm : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [hm, FrameDegreeData.gram_mul, hx τ] at hG
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hc : ((yM X w τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (yM X w τ).det :=
    (RingHom.map_det (starRingEnd ℂ) (yM X w τ)).symm
  rw [hc] at hd
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by exact_mod_cast PoinPf.sgn_ne _ _
  have hY : (yM X w τ).det = ((∏ k, gsS X w τ k : ℝ) : ℂ) := by
    rw [yM, Matrix.det_mul, gsB, Matrix.det_mul, Matrix.det_diagonal]
    rw [Matrix.det_of_lowerTriangular _ (fun a b hab => ?_)]
    · rw [gsU, Matrix.det_of_upperTriangular (FrameDegreeData.uMat_upper _)]
      simp only [FrameDegreeData.uMat_diag, Finset.prod_const_one, one_mul]
      have : ∀ i, mat (nmat X w) τ i i = 1 := fun i => by
        simp [mat, nmat]
      simp only [this, Finset.prod_const_one, one_mul]
      push_cast; rfl
    · show nmat X w τ a b = 0
      simp only [nmat]
      have hab' : a < b := hab
      have h1 : ¬ b < a := not_lt.2 (le_of_lt hab')
      rw [dif_neg h1, if_neg (ne_of_lt hab')]
  set t : ℝ := ∏ k, gsS X w τ k with ht
  have hpos : 0 ≤ t := Finset.prod_nonneg fun k _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hY, Complex.conj_ofReal] at hd
  have htt : ((t * t : ℝ) : ℂ) = 1 := by
    have h2 : (t : ℂ) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det * (t : ℂ) =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [hd, one_mul]
    push_cast
    have h3 : ((t : ℂ) * t) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [← h2]; ring
    exact mul_right_cancel₀ hJ h3
  have htt' : t * t = 1 := by exact_mod_cast htt
  have ht1 : t = 1 := by nlinarith
  rw [secM, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))) (yM X w τ), hY, ht1, Complex.ofReal_one]

end GlobalTheory.SUChartSection
