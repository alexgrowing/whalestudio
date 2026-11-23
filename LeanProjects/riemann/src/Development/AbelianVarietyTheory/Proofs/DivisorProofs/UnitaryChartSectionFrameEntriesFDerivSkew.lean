import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_gram_entry (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {R : ℝ}
    (hR : ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom) {w : V (nd X)}
    (hw : w ∈ Metric.ball (0 : V (nd X)) R) (τ : X.Ψ) (a b : Fin r) :
    ∑ k, yF X w τ k a * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) * conj (yF X w τ k b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h1 := FrameDegreeData.ortho_bOf X (hR w hw) τ
  rw [bOf_cpt X hx w] at h1
  have h2 : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [h2, FrameDegreeData.gram_mul, hx τ] at h1
  have h3 := congrFun (congrFun h1 a) b
  rw [Matrix.mul_apply] at h3
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply] at h3
  rw [← h3]
  rfl

theorem dY_skew (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  obtain ⟨R, hR, hdom⟩ := exists_ball X hx
  set ε : Fin r → ℂ := fun k => ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) with hε
  have hY : HasFDerivAt (yF X) (dY X) 0 := hd.hasFDerivAt
  let P : Fin r → Fin r → (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ := fun k c =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) c).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : ∀ k c, HasFDerivAt (fun w => yF X w τ k c) ((P k c).comp (dY X)) 0 :=
    fun k c => (P k c).hasFDerivAt.comp 0 hY
  have hcc : ∀ k c, HasFDerivAt (fun w => conj (yF X w τ k c))
      ((Complex.conjCLE.toContinuousLinearMap).comp ((P k c).comp (dY X))) 0 :=
    fun k c => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp 0 (hc k c)
  have hf := HasFDerivAt.sum (u := Finset.univ) fun k _ => ((hc k a).mul_const (ε k)).mul (hcc k b)
  have hconst : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b))
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    refine (hasFDerivAt_const (if a = b then ε a else 0) (0 : V (nd X))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with w hw
    exact yF_gram_entry X hx hdom hw τ a b
  have hf' : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b)) _ 0 :=
    hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [Finset.sum_apply])
  have key := congrArg (fun L => L z) (hf'.unique hconst)
  have h0 : ∀ k c, yF X 0 τ k c = if k = c then 1 else 0 := by
    intro k c
    show yM X 0 τ k c = _
    rw [yM_zero, Matrix.one_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, h0] at key
  simp only [ite_mul, one_mul, zero_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, P, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at key
  linear_combination key

end GlobalTheory.SUChartSection
