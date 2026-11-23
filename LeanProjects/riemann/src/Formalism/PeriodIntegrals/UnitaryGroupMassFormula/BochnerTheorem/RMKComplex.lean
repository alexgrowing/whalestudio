import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BochnerTheorem.StepGelfand

noncomputable section

open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported

namespace PI.Bochner

variable {X : Type*} [TopologicalSpace X]

def ofR (g : C(X, ℝ)) : C(X, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩

@[simp] lemma ofR_apply (g : C(X, ℝ)) (x : X) : ofR g x = (g x : ℂ) := rfl

lemma ofR_add (g h : C(X, ℝ)) : ofR (g + h) = ofR g + ofR h := by
  ext x
  simp

lemma ofR_sub (g h : C(X, ℝ)) : ofR (g - h) = ofR g - ofR h := by
  ext x
  simp

lemma ofR_smul (c : ℝ) (g : C(X, ℝ)) : ofR (c • g) = (c : ℂ) • ofR g := by
  ext x
  simp

def reC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩

def imC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩

lemma eq_ofR_re_add_im (f : C(X, ℂ)) : f = ofR (reC f) + Complex.I • ofR (imC f) := by
  ext x
  apply Complex.ext <;> simp [reC, imC]

section
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ

lemma nonneg_ofR {g : C(X, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ Λ (ofR g) := by
  have e : ofR g = star (ofR ⟨fun x => Real.sqrt (g x), by fun_prop⟩) *
      ofR ⟨fun x => Real.sqrt (g x), by fun_prop⟩ := by
    ext x
    simp only [ofR_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.coe_mk,
      Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg x)]
  rw [e]
  exact hΛ _

lemma im_ofR (g : C(X, ℝ)) : (Λ (ofR g)).im = 0 := by
  have hp : ∀ h : C(X, ℝ), (∀ x, 0 ≤ h x) → (Λ (ofR h)).im = 0 := fun h hh =>
    ((Complex.nonneg_iff.1 (nonneg_ofR Λ hΛ hh)).2).symm
  rw [← posPart_sub_negPart g, ofR_sub, map_sub, Complex.sub_im,
    hp _ (fun x => ContinuousMap.le_def.1 (posPart_nonneg g) x),
    hp _ (fun x => ContinuousMap.le_def.1 (negPart_nonneg g) x), sub_zero]

lemma ofR_eq_re (g : C(X, ℝ)) : Λ (ofR g) = ((Λ (ofR g)).re : ℂ) := by
  exact Complex.ext (by simp) (by simp [im_ofR Λ hΛ g])

end

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem exists_measure_of_positive (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ := by
  let e := CompactlySupportedContinuousMap.continuousMapEquiv (α := X) (β := ℝ)
  let L : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun f => (Λ (ofR (e.symm f))).re
      map_add' := fun f g => by
        have h1 : e.symm (f + g) = e.symm f + e.symm g := by ext x; simp [e]
        simp only [h1, ofR_add, map_add, Complex.add_re]
      map_smul' := fun c f => by
        have h1 : e.symm (c • f) = c • e.symm f := by ext x; simp [e]
        simp only [h1, ofR_smul, map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply] }
  let Lp := PositiveLinearMap.mk₀ L (fun f hf => by
    show 0 ≤ (Λ (ofR (e.symm f))).re
    have hfx : ∀ x, 0 ≤ (e.symm f) x := fun x => by
      have h2 : (0 : CompactlySupportedContinuousMap X ℝ) x ≤ f x := hf x
      simpa [e] using h2
    exact (Complex.nonneg_iff.1 (nonneg_ofR Λ hΛ hfx)).1)
  refine ⟨RealRMK.rieszMeasure Lp, inferInstance, fun f => ?_⟩
  have hint : ∀ g : C(X, ℝ), ∫ x, g x ∂(RealRMK.rieszMeasure Lp) = (Λ (ofR g)).re := fun g => by
    have h := RealRMK.integral_rieszMeasure Lp (e g)
    have h3 : e.symm (e g) = g := e.symm_apply_apply g
    simp only [e, CompactlySupportedContinuousMap.continuousMapEquiv_apply_toFun] at h
    rw [h]
    show (Λ (ofR (e.symm (e g)))).re = _
    rw [h3]
  have hI : Integrable (fun x => f x) (RealRMK.rieszMeasure Lp) := by
    first
      | exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      | exact ContinuousMap.integrable f
      | exact (integrableOn_univ).1 (f.continuous.continuousOn.integrableOn_compact isCompact_univ)
  conv_lhs => rw [eq_ofR_re_add_im f]
  rw [map_add, map_smul, ofR_eq_re Λ hΛ, ofR_eq_re Λ hΛ (imC f), ← hint, ← hint, smul_eq_mul,
    ← integral_re_add_im hI]
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex]
  rw [mul_comm]
  rfl

end PI.Bochner
