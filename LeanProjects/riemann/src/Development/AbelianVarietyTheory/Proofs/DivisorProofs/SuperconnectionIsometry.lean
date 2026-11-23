import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

open Filter Topology Set

namespace GlobalTheory.TorsionForm.Gauge

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem fderiv_real_I_smul {φ : Pt E g → ℂ} {P : Pt E g} (hφ : DifferentiableAt ℂ φ P) (v : Pt E g) :
    fderiv ℝ φ P (Complex.I • v) = Complex.I * fderiv ℝ φ P v := by
  rw [(hφ.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp

theorem dholo_dbar_smul_holomorphic {m : ℕ} {φ : Pt E g → ℂ} {s : Pt E g → Ext m} {P : Pt E g}
    (hφ : DifferentiableAt ℂ φ P) (hs : DifferentiableAt ℝ s P) (v : Pt E g) :
    d10 (fun Q => φ Q • s Q) P v = φ P • d10 s P v + fderiv ℝ φ P v • s P ∧
    d01 (fun Q => φ Q • s Q) P v = φ P • d01 s P v := by
  have hφR : DifferentiableAt ℝ φ P := hφ.restrictScalars ℝ
  have e : fderiv ℝ (fun Q => φ Q • s Q) P = φ P • fderiv ℝ s P + (fderiv ℝ φ P).smulRight (s P) :=
    fderiv_smul hφR hs
  have hI := fderiv_real_I_smul hφ v
  constructor
  · funext S
    simp only [d10, e, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, hI, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  · funext S
    simp only [d01, e, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, hI, Pi.add_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring

theorem dholo_log_isometry {B : Set E} {h h' : Pt E g → ℝ} {φ : Pt E g → ℂ} {P : Pt E g}
    (hB : IsOpen B) (hP : P ∈ cov B g) (hφ : DifferentiableAt ℂ φ P)
    (hφ0 : ∀ Q ∈ cov B g, φ Q ≠ 0) (hh0 : ∀ Q ∈ cov B g, 0 < h Q) (hh : DifferentiableAt ℝ h P)
    (hiso : IsIsometry B h h' φ) (v : Pt E g) :
    d10 (fun Q => (Real.log (h' Q) : ℂ)) P v =
      d10 (fun Q => (Real.log (h Q) : ℂ)) P v - fderiv ℝ φ P v / φ P := by
  have hO : IsOpen (cov B g) := hB.prod isOpen_univ
  have hN : cov B g ∈ 𝓝 P := hO.mem_nhds hP
  have hφR : DifferentiableAt ℝ φ P := hφ.restrictScalars ℝ
  set ψ : Pt E g → ℂ := fun Q => φ Q * star (φ Q) with hψ
  set D := fderiv ℝ φ P with hD
  have hψd : HasFDerivAt ψ (φ P • ((starL' ℝ : ℂ ≃L⋆[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp D + star (φ P) • D) P :=
    hφR.hasFDerivAt.mul hφR.hasFDerivAt.star
  have hψP : ψ P = (Complex.normSq (φ P) : ℂ) := by
    simp only [hψ]; rw [← Complex.mul_conj]; rfl
  have hpos : 0 < Complex.normSq (φ P) := Complex.normSq_pos.2 (hφ0 P hP)
  have hslit : ψ P ∈ Complex.slitPlane := by
    rw [hψP]; exact Complex.ofReal_mem_slitPlane.2 hpos
  have hlog : HasFDerivAt (fun Q => Complex.log (ψ Q))
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ψ P)⁻¹).restrictScalars ℝ).comp
        (φ P • ((starL' ℝ : ℂ ≃L⋆[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp D + star (φ P) • D)) P :=
    ((Complex.hasStrictDerivAt_log hslit).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp P hψd
  have hL : DifferentiableAt ℝ (fun Q => (Real.log (h Q) : ℂ)) P :=
    Complex.ofRealCLM.differentiableAt.comp P (hh.log (hh0 P hP).ne')
  have heq : (fun Q => (Real.log (h' Q) : ℂ)) =ᶠ[𝓝 P]
      fun Q => (Real.log (h Q) : ℂ) - Complex.log (ψ Q) := by
    filter_upwards [hN] with Q hQ
    have h0 := hφ0 Q hQ
    have hq : 0 < Complex.normSq (φ Q) := Complex.normSq_pos.2 h0
    have hi := hiso Q hQ
    have hn : ‖φ Q‖ ^ 2 = Complex.normSq (φ Q) := (Complex.normSq_eq_norm_sq _).symm
    have hψQ : ψ Q = (Complex.normSq (φ Q) : ℂ) := by
      simp only [hψ]; rw [← Complex.mul_conj]; rfl
    have h'Q : h' Q = h Q / Complex.normSq (φ Q) := by
      rw [← hn, ← hi, mul_div_cancel_right₀]; rw [hn]; exact hq.ne'
    rw [hψQ, ← Complex.ofReal_log hq.le, h'Q, Real.log_div (hh0 Q hQ).ne' hq.ne', Complex.ofReal_sub]
  have hF := (hL.hasFDerivAt.sub hlog).congr_of_eventuallyEq heq
  have hI : D (Complex.I • v) = Complex.I * D v := fderiv_real_I_smul hφ v
  have hφP := hφ0 P hP
  have hsφ : (starRingEnd ℂ) (φ P) ≠ 0 := (map_ne_zero _).2 hφP
  simp only [d10, hF.fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe,
    starL'_apply, hI, smul_eq_mul, hψ, star_mul', Complex.star_def, map_mul, Complex.conj_I]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem connection_isometry_smul {n : ℕ} {B : Set E} {h h' : Pt E g → ℝ} {φ : Pt E g → ℂ} {P : Pt E g}
    {s : Pt E g → Ext (n + n + g)}
    (hB : IsOpen B) (hP : P ∈ cov B g) (hφ : DifferentiableAt ℂ φ P)
    (hφ0 : ∀ Q ∈ cov B g, φ Q ≠ 0) (hh0 : ∀ Q ∈ cov B g, 0 < h Q) (hh : DifferentiableAt ℝ h P)
    (hiso : IsIsometry B h h' φ) (hs : DifferentiableAt ℝ s P) (v : Pt E g) :
    pointDifference h' (fun Q => φ Q • s Q) P v = φ P • pointDifference h s P v := by
  have e1 := (dholo_dbar_smul_holomorphic hφ hs v).1
  have e2 := dholo_log_isometry hB hP hφ hφ0 hh0 hh hiso v
  have hφP := hφ0 P hP
  funext S
  simp only [pointDifference, e1, e2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem superconn_isometry_smul (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g n : ℕ)
    (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h h' : Pt E g → ℝ) (φ : Pt E g → ℂ)
    (β : Fin n → E) (u : ℝ) (s : Pt E g → Ext (n + n + g)) (P : Pt E g) (hB : IsOpen B)
    (hP : P ∈ cov B g) (hφd : DifferentiableOn ℂ φ (cov B g)) (hφ0 : ∀ Q ∈ cov B g, φ Q ≠ 0)
    (hh0 : ∀ Q ∈ cov B g, 0 < h Q) (hh : DifferentiableAt ℝ h P) (hiso : IsIsometry B h h' φ)
    (hs : DifferentiableAt ℝ s P) :
    superconn τ h' β u (fun Q => φ Q • s Q) P = φ P • superconn τ h β u s P := by
  have hφ : DifferentiableAt ℂ φ P := hφd.differentiableAt ((hB.prod isOpen_univ).mem_nhds hP)
  have e1 : ∀ v, pointDifference h' (fun Q => φ Q • s Q) P v = φ P • pointDifference h s P v :=
    connection_isometry_smul hB hP hφ hφ0 hh0 hh hiso hs
  have e2 : ∀ v, d01 (fun Q => φ Q • s Q) P v = φ P • d01 s P v := fun v => (dholo_dbar_smul_holomorphic hφ hs v).2
  simp only [superconn, nablaE, dbarV, dbarAdj, e1, e2, connForm_smul, wedge_smul, contr_smul,
    ← smul_add, Finset.smul_sum, smul_neg, smul_comm (φ P)]
  funext S
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Finset.mul_sum,
    mul_add, mul_neg, mul_left_comm]

end GlobalTheory.TorsionForm.Gauge
