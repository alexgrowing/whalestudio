import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm Filter Topology Polynomial

noncomputable section

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_apply_eq_deriv_deriv {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (v : E) :
    fderiv ℝ (fderiv ℝ φ) 0 v v = deriv (deriv fun t : ℝ => φ (t • v)) 0 := by
  have hev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • v) v t := fun t => by
    simpa using (hasDerivAt_id t).smul_const v
  have hline : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => t • v := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hder : (deriv fun t : ℝ => φ (t • v)) =ᶠ[𝓝 0] fun t => fderiv ℝ φ (t • v) v := by
    filter_upwards [hline.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hlin t)).deriv
  rw [hder.deriv_eq]
  have h2 : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h3 : HasDerivAt ((fderiv ℝ φ) ∘ fun t : ℝ => t • v) (fderiv ℝ (fderiv ℝ φ) 0 v) 0 :=
    h2.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hlin 0) (by simp)
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using h4.deriv.symm

end Line

section Levi

variable {ι : Type*} [Fintype ι]

theorem levi_finset_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → ℂ) → ℝ)
    (hF : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) 0) (w : ι → ℂ) :
    levi (fun z => ∑ j ∈ s, F j z) 0 w = ∑ j ∈ s, levi (F j) 0 w := by
  have hev : ∀ᶠ z in 𝓝 (0 : ι → ℂ), ∀ j ∈ s, DifferentiableAt ℝ (F j) z := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ((hF j hj).eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have h1 : fderiv ℝ (fun z => ∑ j ∈ s, F j z) =ᶠ[𝓝 0] fun z => ∑ j ∈ s, fderiv ℝ (F j) z := by
    filter_upwards [hev] with z hz
    simpa only [Finset.sum_fn] using fderiv_sum hz
  have h2 : fderiv ℝ (fderiv ℝ fun z => ∑ j ∈ s, F j z) 0 =
      ∑ j ∈ s, fderiv ℝ (fderiv ℝ (F j)) 0 := by
    rw [h1.fderiv_eq]
    simpa only [Finset.sum_fn] using fderiv_sum fun j hj =>
      ((hF j hj).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  simp only [levi, h2, _root_.sum_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_div]

theorem levi_eq_deriv_deriv {φ : (ι → ℂ) → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv fun t : ℝ => φ (t • w)) 0 +
      deriv (deriv fun t : ℝ => φ (t • (Complex.I • w))) 0) / 4 := by
  simp only [levi, fderiv_fderiv_apply_eq_deriv_deriv hφ]

end Levi

section LogPoly

theorem deriv_deriv_log_norm_eval (Q : ℂ[X]) (h0 : Q.coeff 0 = 1) (h1 : Q.coeff 1 = 0) :
    deriv (deriv fun t : ℝ => Real.log ‖Q.eval (t : ℂ)‖) 0 = 2 * (Q.coeff 2).re := by
  set f : ℝ → ℂ := fun t => Q.eval (t : ℂ) with hfdef
  have hf : ∀ t : ℝ, HasDerivAt f (Q.derivative.eval (t : ℂ)) t := fun t =>
    (Q.hasDerivAt (t : ℂ)).comp_ofReal
  have hf' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Q.derivative.eval (t : ℂ))
      (Q.derivative.derivative.eval (t : ℂ)) t := fun t =>
    (Q.derivative.hasDerivAt (t : ℂ)).comp_ofReal
  have hf0 : f 0 = 1 := by simp [f, ← Polynomial.coeff_zero_eq_eval_zero, h0]
  have hslit : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Complex.slitPlane := by
    have hc : Continuous f := Q.continuous.comp Complex.continuous_ofReal
    exact hc.continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds (by rw [hf0]; exact Complex.one_mem_slitPlane))
  have hD : (deriv fun t : ℝ => Real.log ‖f t‖) =ᶠ[𝓝 0]
      fun t => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t) := by
    filter_upwards [hslit] with t ht
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hf t).clog_real ht)
    have he : (fun t : ℝ => Real.log ‖f t‖) = Complex.reCLM ∘ fun t => Complex.log (f t) := by
      funext t; simp [Complex.log_re]
    rw [he]; exact h2.deriv
  rw [hD.deriv_eq]
  have hq := (hf' 0).div (hf 0) (by rw [hf0]; exact one_ne_zero)
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  rw [show (fun t : ℝ => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t)) =
    Complex.reCLM ∘ ((fun t : ℝ => Q.derivative.eval (t : ℂ)) / f) from rfl, h3.deriv]
  have e1 : Q.derivative.eval ((0 : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp [h1]
  have e2 : Q.derivative.derivative.eval ((0 : ℝ) : ℂ) = 2 * Q.coeff 2 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    norm_num [mul_comm]
  rw [hf0, e1, e2]
  simp

end LogPoly

end

end GroundTheory.Heights₂.Heights.FourB
