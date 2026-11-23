import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtTwoOfDifferentiableOnOpenStatement
open Matrix Filter Topology GlobalTheory.HermFrame

namespace GlobalTheory.ImSymmChTwo

open Complex ComplexConjugate

theorem trace_sym_combo {n : Type} [Fintype n] {P A₁ A₂ B₁ B₂ : Matrix n n ℂ}
    (hP : Pᵀ = P) (hA₁ : A₁ᵀ = A₁) (hA₂ : A₂ᵀ = A₂) (hB₁ : B₁ᵀ = B₁) (hB₂ : B₂ᵀ = B₂) :
    (P * B₁ * P * A₁ * (P * B₂ * P * A₂)).trace + (P * B₂ * P * A₂ * (P * B₁ * P * A₁)).trace
      - (P * B₂ * P * A₁ * (P * B₁ * P * A₂)).trace
      - (P * B₁ * P * A₂ * (P * B₂ * P * A₁)).trace = 0 := by
  have e1 : (P * B₂ * P * A₂ * (P * B₁ * P * A₁)).trace =
      (P * B₁ * P * A₁ * (P * B₂ * P * A₂)).trace := trace_mul_comm _ _
  have e2 : (P * B₁ * P * A₂ * (P * B₂ * P * A₁)).trace =
      (P * B₂ * P * A₁ * (P * B₁ * P * A₂)).trace := trace_mul_comm _ _
  have e3 : (P * B₂ * P * A₁ * (P * B₁ * P * A₂)).trace =
      (P * B₁ * P * A₁ * (P * B₂ * P * A₂)).trace := by
    rw [← trace_transpose]
    simp only [transpose_mul, hP, hA₁, hA₂, hB₁, hB₂, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3]; ring

theorem chTwo_im_eq_zero_of_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} {Z : E → Matrix (Fin g) (Fin g) ℂ} {w : E}
    (hC : ∀ i k, ContDiffAt ℂ 2 (fun x => Z x i k) w) (hS : ∀ᶠ x in 𝓝 w, (Z x).IsSymm)
    (hu : IsUnit ((Z w).map fun c => ((c.im : ℝ) : ℂ)).det) (ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo (fun x => (Z x).map fun c => ((c.im : ℝ) : ℂ)) w ξ₁ η₁ ξ₂ η₂ = 0 := by
  set Y : E → Matrix (Fin g) (Fin g) ℂ := fun x => (Z x).map fun c => ((c.im : ℝ) : ℂ) with hYdef
  have hY2 : MContDiffAt 2 Y w := fun i k =>
    (ofRealCLM.comp imCLM).contDiff.contDiffAt.comp w ((hC i k).restrict_scalars ℝ)
  have hsym : ∀ᶠ x in 𝓝 w, (Y x).IsSymm := hS.mono fun x hx => hx.map _
  have hdd : ∀ ξ η, mddbar Y w ξ η = 0 := fun ξ η => by
    ext i k
    have h := leviForm_re_eq_zero (f := fun x => -I * Z x i k) (contDiffAt_const.mul (hC i k))
    have e : (fun x => ((Z x i k).im : ℂ)) = fun x => (((-I * Z x i k).re : ℝ) : ℂ) := by
      funext x; simp
    have h2 : ddbar (fun x => ((Z x i k).im : ℂ)) w = 0 := by rw [e]; exact h
    simp only [mddbar_apply, Matrix.zero_apply, hYdef, Matrix.map_apply, h2,
      ContinuousLinearMap.zero_apply]
  have hdel : ∀ ξ, (mdel Y w ξ)ᵀ = mdel Y w ξ := fun ξ => by
    rw [← mdel_transpose]; exact mdel_congr (hsym.mono fun x hx => hx.eq) ξ
  have hdbar : ∀ η, (mdbar Y w η)ᵀ = mdbar Y w η := fun η => by
    rw [← mdbar_transpose]; exact mdbar_congr (hsym.mono fun x hx => hx.eq) η
  have hP : ((Y w)ᵀ⁻¹)ᵀ = (Y w)ᵀ⁻¹ := by
    rw [hsym.self_of_nhds.eq, transpose_nonsing_inv, hsym.self_of_nhds.eq]
  have hF : ∀ ξ η, curv Y w ξ η = (Y w)ᵀ⁻¹ * mdbar Y w η * (Y w)ᵀ⁻¹ * mdel Y w ξ := fun ξ η => by
    rw [curv_eq hY2 hu, hdd, transpose_zero, Matrix.mul_zero, sub_zero, hdel, hdbar]
  have htr : chTwo Y w ξ₁ η₁ ξ₂ η₂ = kappa ^ 2 / 2 *
      ((curv Y w ξ₁ η₁ * curv Y w ξ₂ η₂).trace + (curv Y w ξ₂ η₂ * curv Y w ξ₁ η₁).trace
        - (curv Y w ξ₁ η₂ * curv Y w ξ₂ η₁).trace - (curv Y w ξ₂ η₁ * curv Y w ξ₁ η₂).trace) := by
    simp only [chTwo, wedge, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  rw [htr, hF, hF, hF, hF, trace_sym_combo hP (hdel ξ₁) (hdel ξ₂) (hdbar η₁) (hdbar η₂), mul_zero]

theorem chTwo_im_eq_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {g : ℕ} {Z : E → Matrix (Fin g) (Fin g) ℂ} {W : Set E} {w : E}
    (hW : IsOpen W) (hw : w ∈ W) (hZ : ∀ i k, DifferentiableOn ℂ (fun x => Z x i k) W)
    (hS : ∀ x ∈ W, (Z x).IsSymm) (hu : IsUnit ((Z w).map fun c => ((c.im : ℝ) : ℂ)).det)
    (ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo (fun x => (Z x).map fun c => ((c.im : ℝ) : ℂ)) w ξ₁ η₁ ξ₂ η₂ = 0 :=
  chTwo_im_eq_zero_of_contDiffAt (fun i k => GlobalTheory.T.contDiffAt_two_of_differentiableOn_open hW hw (hZ i k))
    (Filter.mem_of_superset (hW.mem_nhds hw) hS) hu ξ₁ η₁ ξ₂ η₂

end GlobalTheory.ImSymmChTwo
