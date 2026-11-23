import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff Topology

noncomputable section
namespace GlobalTheory

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem ddc_congr_of_eventuallyEq {u u' : Pt E g → ℝ} {P : Pt E g} (h : u =ᶠ[𝓝 P] u')
    (v w : Pt E g) : ddc u P v w = ddc u' P v w := by
  have h1 : fderiv ℝ u =ᶠ[𝓝 P] fderiv ℝ u' := h.fderiv
  have hz : ∀ z : Pt E g, (fun Q => fderiv ℝ u Q (Complex.I • z)) =ᶠ[𝓝 P]
      fun Q => fderiv ℝ u' Q (Complex.I • z) := fun z => h1.mono fun Q hQ => by simp only [hQ]
  unfold ddc
  rw [(hz v).fderiv_eq, (hz w).fderiv_eq]

theorem ddc_re_eq_zero {f : Pt E g → ℂ} {P : Pt E g} (hf : AnalyticAt ℂ f P) (v w : Pt E g) :
    ddc (fun Q => (f Q).re) P v w = 0 := by
  have hev : ∀ᶠ Q in 𝓝 P, AnalyticAt ℂ f Q := hf.eventually_analyticAt
  have key : ∀ z : Pt E g, (fun Q => fderiv ℝ (fun Q => (f Q).re) Q (Complex.I • z)) =ᶠ[𝓝 P]
      fun Q => -(fderiv ℂ f Q z).im := by
    intro z
    filter_upwards [hev] with Q hQ
    have hd : HasFDerivAt f (fderiv ℂ f Q) Q := hQ.differentiableAt.hasFDerivAt
    have hr : HasFDerivAt (fun Q => (f Q).re)
        (Complex.reCLM.comp ((fderiv ℂ f Q).restrictScalars ℝ)) Q :=
      Complex.reCLM.hasFDerivAt.comp Q (hd.restrictScalars ℝ)
    rw [hr.fderiv]
    simp
  set D := fderiv ℂ (fderiv ℂ f) P
  have hD : ∀ z : Pt E g, HasFDerivAt (fun Q => -(fderiv ℂ f Q z).im)
      (-(Complex.imCLM.comp (((ContinuousLinearMap.apply ℂ ℂ z).comp D).restrictScalars ℝ))) P := by
    intro z
    have h2 : HasFDerivAt (fderiv ℂ f) D P := hf.fderiv.differentiableAt.hasFDerivAt
    have h3 := (ContinuousLinearMap.apply ℂ ℂ z).hasFDerivAt.comp P h2
    exact (Complex.imCLM.hasFDerivAt.comp P (h3.restrictScalars ℝ)).neg
  have hsymm : IsSymmSndFDerivAt ℂ f P := (hf.contDiffAt (n := ω)).isSymmSndFDerivAt le_top
  unfold ddc
  rw [(key v).fderiv_eq, (key w).fderiv_eq, (hD v).fderiv, (hD w).fderiv]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply, Complex.imCLM_apply]
  rw [hsymm w v]
  ring

end GlobalTheory

namespace GlobalTheory

theorem ddc_log_normSq_eq_zero {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {s : Set (Pt E g)} {φ : Pt E g → ℂ} (hs : IsOpen s)
    (hφ : DifferentiableOn ℂ φ s) (hne : ∀ P ∈ s, φ P ≠ 0) :
    ∀ P ∈ s, ∀ v w : Pt E g, ddc (fun Q => Real.log (‖φ Q‖ ^ 2)) P v w = 0 := by
  intro P hP v w
  set c := φ P with hc
  have hc0 : c ≠ 0 := hne P hP
  set s' := s ∩ {Q | φ Q / c ∈ Complex.slitPlane} with hs'
  have hcont : ContinuousAt (fun Q => φ Q / c) P :=
    (hφ.differentiableAt (hs.mem_nhds hP)).continuousAt.div_const c
  have h1 : φ P / c ∈ Complex.slitPlane := by
    rw [← hc, div_self hc0]; exact Complex.one_mem_slitPlane
  have hs'n : s' ∈ 𝓝 P :=
    Filter.inter_mem (hs.mem_nhds hP) (hcont.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds h1))
  set f : Pt E g → ℂ := fun Q => 2 * Complex.log (φ Q / c) + ((Real.log (‖c‖ ^ 2) : ℝ) : ℂ)
  have hfd : DifferentiableOn ℂ f s' := by
    intro Q hQ
    have hq0 : DifferentiableWithinAt ℂ φ s' Q :=
      (hφ Q hQ.1).mono (fun x hx => hx.1)
    have hq : DifferentiableWithinAt ℂ (fun Q => φ Q / c) s' Q := by
      simpa only [div_eq_mul_inv] using hq0.mul_const c⁻¹
    exact ((hq.clog hQ.2).const_mul 2).add_const _
  have hfa : AnalyticAt ℂ f P := GlobalTheory.SCV.analyticAt_of_differentiableOn hfd hs'n
  have heq : (fun Q => Real.log (‖φ Q‖ ^ 2)) =ᶠ[𝓝 P] fun Q => (f Q).re := by
    filter_upwards [hs'n] with Q hQ
    have hQ0 : φ Q ≠ 0 := hne Q hQ.1
    have e : (f Q).re = 2 * (Complex.log (φ Q / c)).re + Real.log (‖c‖ ^ 2) := by simp [f]
    rw [e, Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hQ0) (norm_ne_zero_iff.mpr hc0),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [ddc_congr_of_eventuallyEq heq, ddc_re_eq_zero hfa]

end GlobalTheory
