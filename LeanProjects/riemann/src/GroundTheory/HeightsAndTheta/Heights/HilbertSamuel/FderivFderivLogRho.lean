import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FSLevi

variable {J : Type} [Fintype J]

def reP (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj p)

def imaginary (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj p)

def nsq (z : J → ℂ) : ℝ := ∑ p, (reP p z ^ 2 + imaginary p z ^ 2)

def bil : (J → ℂ) →L[ℝ] ((J → ℂ) →L[ℝ] ℝ) :=
  ∑ p, ((reP p).smulRight (reP p) + (imaginary p).smulRight (imaginary p))

theorem bil_apply (u v : J → ℂ) : bil u v = ∑ p, (reP p u * reP p v + imaginary p u * imaginary p v) := by
  simp [bil, ContinuousLinearMap.sum_apply]

theorem reP_apply (p : J) (z : J → ℂ) : reP p z = (z p).re := rfl

theorem imaginaryPart_apply (p : J) (z : J → ℂ) : imaginary p z = (z p).im := rfl

theorem hasFDerivAt_nsq (z : J → ℂ) : HasFDerivAt nsq ((2 : ℝ) • bil z) z := by
  have h : ∀ p : J, HasFDerivAt (fun z : J → ℂ ↦ reP p z ^ 2 + imaginary p z ^ 2)
      ((2 * reP p z) • reP p + (2 * imaginary p z) • imaginary p) z := by
    intro p
    have h1 := (reP p).hasFDerivAt (x := z) |>.pow 2
    have h2 := (imaginary p).hasFDerivAt (x := z) |>.pow 2
    refine (h1.add h2).congr_fderiv ?_
    ext v
    simp
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun p _ ↦ h p)
  refine hs.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, bil_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  ring

theorem norm_sq_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem log_rho_eq (z : J → ℂ) : Real.log ((fsMetric J).ρ z) = (1 / 2) * Real.log (nsq z) := by
  have : (fsMetric J).ρ z = Real.sqrt (nsq z) := by
    simp [fsMetric, EuclideanSpace.norm_eq, nsq, reP_apply, imaginaryPart_apply, norm_sq_eq]
  rw [this, Real.log_sqrt (x := nsq z) (Finset.sum_nonneg fun p _ ↦ by positivity)]
  ring

theorem nsq_pos {z : J → ℂ} (hz : z ≠ 0) : 0 < nsq z := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hz
  refine Finset.sum_pos' (fun q _ ↦ by positivity) ⟨p, Finset.mem_univ _, ?_⟩
  rw [reP_apply, imaginaryPart_apply, ← norm_sq_eq]
  exact pow_pos (norm_pos_iff.mpr hp) 2

theorem hasFDerivAt_logRho {z : J → ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun z ↦ Real.log ((fsMetric J).ρ z)) ((nsq z)⁻¹ • bil z) z := by
  have h := ((hasFDerivAt_nsq z).log (nsq_pos hz).ne').const_mul (1 / 2 : ℝ)
  have e : (fun z ↦ Real.log ((fsMetric J).ρ z)) = fun z ↦ (1 / 2) * Real.log (nsq z) :=
    funext log_rho_eq
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_deriv {z : J → ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun z ↦ (nsq z)⁻¹ • bil z)
      ((nsq z)⁻¹ • bil + (((ContinuousLinearMap.toSpanSingleton ℝ (-(nsq z ^ 2)⁻¹)).comp
        ((2 : ℝ) • bil z))).smulRight (bil z)) z := by
  have hinv := (hasFDerivAt_inv (𝕜 := ℝ) (nsq_pos hz).ne').comp z (hasFDerivAt_nsq z)
  exact hinv.fun_smul bil.hasFDerivAt

theorem fderiv_fderiv_logRho {z : J → ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log ((fsMetric J).ρ z)) z =
      (nsq z)⁻¹ • bil + (((ContinuousLinearMap.toSpanSingleton ℝ (-(nsq z ^ 2)⁻¹)).comp
        ((2 : ℝ) • bil z))).smulRight (bil z) := by
  have hev : (fderiv ℝ fun z ↦ Real.log ((fsMetric J).ρ z)) =ᶠ[nhds z]
      fun z ↦ (nsq z)⁻¹ • bil z := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact (hasFDerivAt_logRho hz').fderiv
  rw [hev.fderiv_eq]
  exact (hasFDerivAt_deriv hz).fderiv

theorem cs (z w : J → ℂ) :
    (∑ p, (reP p z * reP p w + imaginary p z * imaginary p w)) ^ 2 +
      (∑ p, (reP p z * reP p (Complex.I • w) + imaginary p z * imaginary p (Complex.I • w))) ^ 2 ≤
      nsq z * nsq w := by
  set a : J → ℂ := fun p ↦ starRingEnd ℂ (z p) * w p
  have h1 : (∑ p, (reP p z * reP p w + imaginary p z * imaginary p w)) = (∑ p, a p).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [a, reP_apply, imaginaryPart_apply, Complex.mul_re]
  have h2 : (∑ p, (reP p z * reP p (Complex.I • w) + imaginary p z * imaginary p (Complex.I • w))) =
      -(∑ p, a p).im := by
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [a, reP_apply, imaginaryPart_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [h1, h2, neg_sq]
  have h3 : (∑ p, a p).re ^ 2 + (∑ p, a p).im ^ 2 = ‖∑ p, a p‖ ^ 2 := (norm_sq_eq _).symm
  rw [h3]
  have h4 : ‖∑ p, a p‖ ≤ ∑ p, ‖z p‖ * ‖w p‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [a]
  have h5 : (∑ p, ‖z p‖ * ‖w p‖) ^ 2 ≤ nsq z * nsq w := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p ↦ ‖z p‖) (fun p ↦ ‖w p‖)
    simpa [nsq, reP_apply, imaginaryPart_apply, norm_sq_eq] using this
  calc ‖∑ p, a p‖ ^ 2 ≤ (∑ p, ‖z p‖ * ‖w p‖) ^ 2 := by gcongr
    _ ≤ nsq z * nsq w := h5

theorem leviForm_nonneg {z : J → ℂ} (hz : z ≠ 0) (w : J → ℂ) :
    0 ≤ leviForm (fun z ↦ Real.log ((fsMetric J).ρ z)) z w := by
  unfold leviForm
  rw [fderiv_fderiv_logRho hz]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hN := nsq_pos hz
  have hww : bil w w = nsq w := by
    rw [bil_apply, nsq]; exact Finset.sum_congr rfl fun p _ ↦ by ring
  have hiw : bil (Complex.I • w) (Complex.I • w) = nsq w := by
    rw [bil_apply, nsq]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [reP_apply, imaginaryPart_apply]
    ring
  rw [hww, hiw]
  have hc := cs z w
  rw [← bil_apply, ← bil_apply] at hc
  set X := bil z w
  set Y := bil z (Complex.I • w)
  have key : (nsq z)⁻¹ * nsq w + (2 * X) * -(nsq z ^ 2)⁻¹ * X +
      ((nsq z)⁻¹ * nsq w + (2 * Y) * -(nsq z ^ 2)⁻¹ * Y) =
        2 * (nsq z * nsq w - (X ^ 2 + Y ^ 2)) / nsq z ^ 2 := by
    field_simp; ring
  have hnn : 0 ≤ 2 * (nsq z * nsq w - (X ^ 2 + Y ^ 2)) / nsq z ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  have : 0 ≤ (nsq z)⁻¹ * nsq w + (2 * X) * -(nsq z ^ 2)⁻¹ * X +
      ((nsq z)⁻¹ * nsq w + (2 * Y) * -(nsq z ^ 2)⁻¹ * Y) := key ▸ hnn
  nlinarith [this]

end FSLevi

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
