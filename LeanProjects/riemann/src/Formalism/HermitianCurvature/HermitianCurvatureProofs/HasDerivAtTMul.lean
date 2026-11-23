import Mathlib

open Set Filter Topology MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def prim (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)

theorem hasDerivAt_t_mul (hω : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} {t : ℝ}
    (hγ : w₀ + (t : ℂ) * (w - w₀) ∈ S) (h : ℂ) :
    HasDerivAt (fun s : ℝ => s * ω (w₀ + (s : ℂ) * (w - w₀)) h)
      (ω (w₀ + (t : ℂ) * (w - w₀)) h + t * fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) h (w - w₀)) t := by
  have hγd : HasDerivAt (fun s : ℝ => w₀ + (s : ℂ) * (w - w₀)) (w - w₀) t := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - w₀)).const_add w₀
    simpa using this
  have h1 : HasDerivAt (fun s : ℝ => ω (w₀ + (s : ℂ) * (w - w₀))) (fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)) t :=
    (hω _ hγ).comp_hasDerivAt t hγd
  have h2 : HasDerivAt (fun s : ℝ => ω (w₀ + (s : ℂ) * (w - w₀)) h)
      (fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀) h) t := by
    exact (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt t h1
  have h3 := (hasDerivAt_id t).mul h2
  refine h3.congr_deriv ?_
  rw [hsym _ hγ h (w - w₀)]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
