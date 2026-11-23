import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun l => conj (v l)) := by
  simp only [hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (u v : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ (gram τ G M *ᵥ fun l => conj (v l)) := by
  have hc : (fun l => conj ((M *ᵥ v) l)) = M.map (starRingEnd ℂ) *ᵥ fun l => conj (v l) := by
    funext l
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dot, hc, FrameDegreeData.gram_eq, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem gram_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (secM X x w τ) = gram τ.1 X.Gm 1 := by
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have hgx : secM X x w τ * mat x τ = mat (rmul (cpt X x w) (FrameDegreeData.bOf X (cpt X x w))) τ := by
    rw [secM, Matrix.nonsing_inv_mul_cancel_right _ _ hu, bOf_cpt X hx, yM, ← Matrix.mul_assoc]
    rfl
  have key : (mat x τ)ᵀ * gram τ.1 X.Gm (secM X x w τ) * (mat x τ).map (starRingEnd ℂ) =
      (mat x τ)ᵀ * gram τ.1 X.Gm 1 * (mat x τ).map (starRingEnd ℂ) := by
    rw [← FrameDegreeData.gram_mul, hgx, FrameDegreeData.ortho_bOf X hw τ, ← hx τ, ← FrameDegreeData.gram_mul, Matrix.one_mul]
  have huT : IsUnit (mat x τ)ᵀ.det := by rwa [Matrix.det_transpose]
  have huC : IsUnit ((mat x τ).map (starRingEnd ℂ)).det := by
    rw [show (mat x τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat x τ) from rfl, ← RingHom.map_det, isUnit_iff_ne_zero, map_ne_zero]
    exact det_ne_of_orth X hx τ
  have h2 := congrArg (fun M => ((mat x τ)ᵀ)⁻¹ * M * ((mat x τ).map (starRingEnd ℂ))⁻¹) key
  simp only [Matrix.mul_assoc] at h2
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ huT, Matrix.mul_nonsing_inv_cancel_right _ _ huC,
    ← Matrix.mul_assoc] using h2

theorem hermC_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  rw [hermC_mulVec, gram_secM X hx hw τ, ← hermC_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SUChartSection
