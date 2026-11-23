import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.LogNormPluriharm

theorem fderiv_fderiv_log_normSq_I_symm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {U : Set V} {φ : V → ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ φ U)
    (h0 : ∀ P ∈ U, φ P ≠ 0) {P : V} (hP : P ∈ U) (v w : V) :
    fderiv ℝ (fun Q => fderiv ℝ (fun Q => Real.log (‖φ Q‖ ^ 2)) Q (Complex.I • v)) P w =
    fderiv ℝ (fun Q => fderiv ℝ (fun Q => Real.log (‖φ Q‖ ^ 2)) Q (Complex.I • w)) P v := by
  have hA : AnalyticOnNhd ℂ φ U := GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hU hd
  have h1 : ∀ Q ∈ U, ∀ a : V, fderiv ℝ (fun Q => Real.log (‖φ Q‖ ^ 2)) Q a
      = (2 * fderiv ℂ φ Q a / φ Q).re := by
    intro Q hQ a
    have hφ : HasFDerivAt φ (fderiv ℂ φ Q) Q := (hA Q hQ).differentiableAt.hasFDerivAt
    have hl := (hφ.restrictScalars ℝ).norm_sq.log (by have := h0 Q hQ; positivity)
    rw [hl.fderiv]
    simp [Complex.div_re, Complex.sq_norm]
    ring
  have hD : HasFDerivAt (fderiv ℂ φ) (fderiv ℂ (fderiv ℂ φ) P) P :=
    (hA P hP).fderiv.differentiableAt.hasFDerivAt
  have hS := ((hA P hP).contDiffAt (n := ω)).isSymmSndFDerivAt le_top
  have hφP : HasFDerivAt φ (fderiv ℂ φ P) P := (hA P hP).differentiableAt.hasFDerivAt
  have key : ∀ a b : V, fderiv ℝ (fun Q => fderiv ℝ (fun Q => Real.log (‖φ Q‖ ^ 2)) Q (Complex.I • a)) P b
      = (2 * Complex.I * (fderiv ℂ (fderiv ℂ φ) P b a * (φ P)⁻¹ - fderiv ℂ φ P a * fderiv ℂ φ P b * ((φ P) ^ 2)⁻¹)).re := by
    intro a b
    have hev : (fun Q => fderiv ℝ (fun Q => Real.log (‖φ Q‖ ^ 2)) Q (Complex.I • a)) =ᶠ[nhds P]
        fun Q => (2 * Complex.I * fderiv ℂ φ Q a * (φ Q)⁻¹).re := by
      filter_upwards [hU.mem_nhds hP] with Q hQ
      rw [h1 Q hQ, ContinuousLinearMap.map_smul, smul_eq_mul]
      ring_nf
    rw [hev.fderiv_eq]
    have hk := ((((hD.clm_apply (hasFDerivAt_const a P)).const_mul (2 * Complex.I)).mul ((hasDerivAt_inv (h0 P hP)).comp_hasFDerivAt P hφP)).restrictScalars ℝ)
    have hr : HasFDerivAt (fun Q => (2 * Complex.I * fderiv ℂ φ Q a * (φ Q)⁻¹).re) _ P := Complex.reCLM.hasFDerivAt.comp P hk
    rw [hr.fderiv, ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
    congr 1
    simp
    ring
  rw [key, key, hS v w]
  congr 1
  ring

theorem ddc_log_norm_sq_eq_zero : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Set (Pt E g)) (φ : Pt E g → ℂ), IsOpen U →
    DifferentiableOn ℂ φ U → (∀ P ∈ U, φ P ≠ 0) → ∀ P ∈ U, ∀ v w : Pt E g,
    ddc (fun Q => Real.log (‖φ Q‖ ^ 2)) P v w = 0 := by
  intro g E _ _ _ U φ hU hd h0 P hP v w
  rw [ddc, fderiv_fderiv_log_normSq_I_symm hU hd h0 hP v w, sub_self, mul_zero]

end GlobalTheory.LogNormPluriharm
