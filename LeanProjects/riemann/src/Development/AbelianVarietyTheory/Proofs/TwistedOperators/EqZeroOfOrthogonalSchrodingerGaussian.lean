import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

open scoped FourierTransform RealInnerProductSpace Real

namespace GlobalTheory.RealWeil

theorem eq_zero_of_inner_rhoSch_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l),
    (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume)
      (k.toLp 2 volume) = 0) → k = 0 := by
  intro l _ k h
  set G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  let m : EuclideanSpace ℝ l → ℂ := fun x => G x * k x
  have hGn : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := Real.pi_pos
    nlinarith [sq_nonneg ‖x‖]
  have hm_cont : Continuous m := G.continuous.mul k.continuous
  have hm_int : Integrable m := k.integrable.norm.mono' hm_cont.aestronglyMeasurable
    (ae_of_all _ fun x => by
      simp only [m, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hGn x))
  have hF : 𝓕 m = 0 := by
    funext q
    have hq := h (Sum.elim 0 (fun i => q i))
    have hp : pPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = 0 := by
      ext i; simp [pPart]
    have hqq : qPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = q := by
      ext i; simp [qPart]
    rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume] at hq
    rw [Real.fourier_eq', Pi.zero_apply, ← hq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [m, coe_rhoSch, rhoFun, phase, hp, hqq, add_zero, inner_zero_left, mul_zero, RCLike.inner_apply,
      map_mul, smul_eq_mul]
    rw [← Complex.exp_conj]
    have hGc : (starRingEnd ℂ) (G x) = G x := by
      rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [hGc]
    have : (starRingEnd ℂ) (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * Complex.I) =
        ((-2 * π * ⟪x, q⟫ : ℝ) : ℂ) * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, real_inner_comm]
      push_cast
      ring
    rw [this]
    ring
  have hm0 : m = 0 := by
    have hi : Integrable (𝓕 m) := by rw [hF]; exact integrable_zero _ _ _
    rw [← hm_cont.fourierInv_fourier_eq hm_int hi, hF]
    funext v
    simp [Real.fourierInv_eq]
  ext x
  have hx := congrFun hm0 x
  simp only [m, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · exfalso
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_eq_zero] at hx
    exact (Real.exp_pos _).ne' hx
  · simpa using hx

end GlobalTheory.RealWeil
