import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Shear

theorem slice_integrable (g : ℝ → ℝ) (hgi : Integrable g) {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    Integrable (fun y : ℝ => g (α * y - c)) := by
  have h1 : Integrable (fun t : ℝ => g (t - c)) := hgi.comp_sub_right c
  exact h1.comp_mul_left' hα

theorem slice_integral (g : ℝ → ℝ) {α : ℝ} (c : ℝ) :
    ∫ y : ℝ, g (α * y - c) = |α⁻¹| * ∫ x, g x := by
  have h1 := Measure.integral_comp_mul_left (fun t : ℝ => g (t - c)) α
  have h2 : ∫ t : ℝ, g (t - c) = ∫ x, g x := integral_sub_right_eq_self g c
  rw [h1, h2, smul_eq_mul]

theorem one_sided (g φ : ℝ → ℝ) (hg : Measurable g) (hφ : Measurable φ)
    (hgi : Integrable g) (hφi : Integrable φ)
    (hg0 : ∀ x, 0 ≤ g x) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (α β : ℝ) (hα : α ≠ 0) :
    Integrable (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)) ∧
    ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      ≤ (∫ x, g x) * (∫ x, φ x) / |α| := by
  set F : ℝ × ℝ → ℝ := fun p => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2) with hF
  have hFm : Measurable F := by
    apply Measurable.mul
    · exact hg.comp (by fun_prop)
    · exact (hφ.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hF0 : ∀ p, 0 ≤ F p := fun p =>
    mul_nonneg (hg0 _) (mul_nonneg (hφ0 _) (hφ0 _))
  set C : ℝ := |α⁻¹| * ∫ x, g x with hC

  have hdom : ∀ x y, F (x, y) ≤ φ x * g (α * y - β * x) := by
    intro x y
    have h1 : φ x * φ y ≤ φ x := by
      have := mul_le_mul_of_nonneg_left (hφ1 y) (hφ0 x)
      simpa using this
    have := mul_le_mul_of_nonneg_left h1 (hg0 (α * y - β * x))
    simpa [hF, mul_comm] using this
  have hslice : ∀ x, Integrable (fun y => F (x, y)) := by
    intro x
    refine Integrable.mono' ((slice_integrable g hgi hα (β * x)).const_mul (φ x))
      (hFm.comp measurable_prodMk_left).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    exact hdom x y
  have hbound : ∀ x, ∫ y, F (x, y) ≤ φ x * C := by
    intro x
    have h1 : ∫ y, F (x, y) ≤ ∫ y, φ x * g (α * y - β * x) :=
      integral_mono (hslice x) ((slice_integrable g hgi hα (β * x)).const_mul (φ x))
        (fun y => hdom x y)
    rw [integral_const_mul, slice_integral] at h1
    exact h1
  have hnn : ∀ x, 0 ≤ ∫ y, F (x, y) := fun x => integral_nonneg (fun y => hF0 _)
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, F (x, y)) volume :=
    (hFm.stronglyMeasurable.integral_prod_right (ν := volume)).aestronglyMeasurable
  have hint : Integrable (fun x => ∫ y, F (x, y)) := by
    refine Integrable.mono' (hφi.mul_const C) hmeas ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
    exact hbound x
  have hFi : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
    have : (fun x => ∫ y, ‖F (x, y)‖) = fun x => ∫ y, F (x, y) := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    rw [this]
    exact hint
  refine ⟨hFi, ?_⟩
  have hval : ∫ p : ℝ × ℝ, F p = ∫ x, ∫ y, F (x, y) := integral_prod F hFi
  have hle : ∫ x, ∫ y, F (x, y) ≤ ∫ x, φ x * C :=
    integral_mono hint (hφi.mul_const C) hbound
  rw [integral_mul_const] at hle
  have hCe : (∫ x, φ x) * C = (∫ x, g x) * (∫ x, φ x) / |α| := by
    rw [hC, abs_inv]
    field_simp
  rw [hval]
  linarith

theorem integral_shear_le (g φ : ℝ → ℝ) (hg : Measurable g) (hφ : Measurable φ)
    (hgi : Integrable g) (hφi : Integrable φ)
    (hg0 : ∀ x, 0 ≤ g x) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    Integrable (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)) ∧
    ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      ≤ (∫ x, g x) * (∫ x, φ x) / max |α| |β| := by
  obtain ⟨hI, hA⟩ := one_sided g φ hg hφ hgi hφi hg0 hφ0 hφ1 α β hα
  obtain ⟨hI', hB'⟩ := one_sided g φ hg hφ hgi hφi hg0 hφ0 hφ1 (-β) (-α) (neg_ne_zero.mpr hβ)
  refine ⟨hI, ?_⟩
  have hsw : ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      = ∫ p : ℝ × ℝ, g (-β * p.2 - -α * p.1) * (φ p.1 * φ p.2) := by
    have h := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun p : ℝ × ℝ => g (α * p.2 - β * p.1) * (φ p.1 * φ p.2))
    rw [Measure.volume_eq_prod, ← h]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Prod.fst_swap, Prod.snd_swap]
    have : α * p.1 - β * p.2 = -β * p.2 - -α * p.1 := by ring
    rw [this, mul_comm (φ p.2)]
  have hB : ∫ p : ℝ × ℝ, g (α * p.2 - β * p.1) * (φ p.1 * φ p.2)
      ≤ (∫ x, g x) * (∫ x, φ x) / |β| := by
    rw [hsw]
    simpa [abs_neg] using hB'
  rcases max_cases |α| |β| with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact hA
  · rw [h]; exact hB

end GlobalTheory.CompanionTheory.Shear
