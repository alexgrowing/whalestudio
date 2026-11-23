import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.UnfoldCplx

variable {α ι : Type} [MeasurableSpace α] [Countable ι]

theorem integrable_comp {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {B : α → ℂ} (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, B (h x) = B x) (i : ι) :
    Integrable (fun x => B (T i x)) (μ.restrict A) := by
  refine ⟨(hB.comp (hT i)).aestronglyMeasurable, ?_⟩
  have h1 := hU (fun x => ‖B x‖ₑ) hB.enorm (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ < ∞ := hBi.2
  have hle : ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ ≤ ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ := by
    rw [h1]; exact ENNReal.le_tsum (f := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ) i
  have hne : ENNReal.ofReal (c i) ≠ 0 := by simpa using hc i
  show ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ < ∞
  by_contra hh
  rw [not_lt, top_le_iff] at hh
  rw [hh, ENNReal.mul_top hne] at hle
  exact absurd (lt_of_le_of_lt hle hfin) (lt_irrefl _)

theorem hasSum_nonneg {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have h1 := hU (fun x => ENNReal.ofReal (g x)) hg.ennreal_ofReal (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ENNReal.ofReal (g x) ∂μ ≠ ∞ := (hgi.lintegral_lt_top).ne
  set F : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ENNReal.ofReal (g (T i x)) ∂μ with hF
  have hsum : ∑' i, F i ≠ ∞ := by rw [← h1]; exact hfin
  have hFi : ∀ i, F i ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hsum
  have key := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq hFi, ← h1, ← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hg0) hg.aestronglyMeasurable] at key
  convert key using 1
  funext i
  simp only [hF, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc i).le]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hg0 _))
    (hg.comp (hT i)).aestronglyMeasurable]

theorem hasSum_real {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hgi : Integrable g (μ.restrict 𝓕))
    (hgA : ∀ i, Integrable (fun x => g (T i x)) (μ.restrict A))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have hp := hasSum_nonneg hc hT hU (g := fun x => max (g x) 0) (hg.max measurable_const)
    (fun x => le_max_right _ _) hgi.pos_part (fun h hh x => by simp only [hH h hh x])
  have hn := hasSum_nonneg hc hT hU (g := fun x => max (-g x) 0) (hg.neg.max measurable_const)
    (fun x => le_max_right _ _) hgi.neg_part (fun h hh x => by simp only [hH h hh x])
  have hsplit : ∀ y : ℝ, max y 0 - max (-y) 0 = y := fun y => by
    rcases le_total y 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have e1 : ∫ x in 𝓕, g x ∂μ = (∫ x in 𝓕, max (g x) 0 ∂μ) - ∫ x in 𝓕, max (-g x) 0 ∂μ := by
    rw [← integral_sub hgi.pos_part hgi.neg_part]; simp only [hsplit]
  have hf : (fun i => c i * ∫ x in A, g (T i x) ∂μ) = fun i =>
      c i * (∫ x in A, max (g (T i x)) 0 ∂μ) - c i * ∫ x in A, max (-g (T i x)) 0 ∂μ := by
    funext i
    rw [← mul_sub, ← integral_sub (hgA i).pos_part (hgA i).neg_part]; simp only [hsplit]
  rw [e1, hf]
  exact hp.sub hn

theorem hasSum_complex : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  intro α ι _ _ μ 𝓕 A c hc T hT H hU B hB hBi hH
  have hBA := integrable_comp hc hT hU hB hBi hH
  refine ⟨hBA, ?_⟩
  rw [Complex.hasSum_iff]
  constructor
  · have := hasSum_real hc hT hU (g := fun x => (B x).re) (Complex.measurable_re.comp hB) hBi.re
      (fun i => (hBA i).re) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).re ∂μ = (∫ x in 𝓕, B x ∂μ).re := integral_re hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).re ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).re := by
      funext i
      rw [Complex.re_ofReal_mul]; congr 1; exact integral_re (hBA i)
    rw [e2, hf] at this
    exact this
  · have := hasSum_real hc hT hU (g := fun x => (B x).im) (Complex.measurable_im.comp hB) hBi.im
      (fun i => (hBA i).im) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).im ∂μ = (∫ x in 𝓕, B x ∂μ).im := integral_im hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).im ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).im := by
      funext i
      rw [Complex.im_ofReal_mul]; congr 1; exact integral_im (hBA i)
    rw [e2, hf] at this
    exact this

end GlobalTheory.UnfoldCplx
