import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory

theorem product_bound_of_factor_bounds {G : Type} [Group G] (P : Subgroup G) {X : Type} [MeasurableSpace X] (μ : Measure X) (a : X → G) (δ : P → ℝ≥0)
    (H : ∀ Φ : G → ℝ≥0∞, (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
      (∀ g : G, AEMeasurable (fun x => Φ (a x * g)) μ) → ∀ g : G, ∫⁻ x, Φ (a x * g) ∂μ = ∫⁻ x, Φ (a x) ∂μ)
    (f : G → ℝ) (hint : ∀ g : G, Integrable (fun x => f (a x * g)) μ)
    (heq : ∀ (p : P) (g : G), f ((p : G) * g) = (δ p : ℝ) * f g) (g : G) :
    ∫ x, f (a x * g) ∂μ = ∫ x, f (a x) ∂μ := by
  have key : ∀ h : G → ℝ, (∀ (p : P) (g : G), h ((p : G) * g) = (δ p : ℝ) * h g) →
      (∀ g, AEMeasurable (fun x => h (a x * g)) μ) →
      ∫⁻ x, ENNReal.ofReal (h (a x * g)) ∂μ = ∫⁻ x, ENNReal.ofReal (h (a x)) ∂μ := by
    intro h hh hm
    exact H (fun y => ENNReal.ofReal (h y)) (fun p y => by
      simp only [hh, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal])
      (fun y => (hm y).ennreal_ofReal) g
  have h1 := key f heq (fun y => (hint y).aestronglyMeasurable.aemeasurable)
  have h2 := key (fun y => - f y) (fun p y => by simp [heq])
    (fun y => (hint y).aestronglyMeasurable.aemeasurable.neg)
  have hint1 : Integrable (fun x => f (a x)) μ := by simpa using hint 1
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint g),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint1]
  rw [h1, h2]

theorem lintegral_translation_identity_to_complex : ∀ (G : Type) [Group G] (P : Subgroup G) (X : Type) [MeasurableSpace X] (μ : Measure X) (a : X → G) (δ : P → ℝ≥0),
    (∀ Φ : G → ℝ≥0∞, (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
      (∀ g : G, AEMeasurable (fun x => Φ (a x * g)) μ) → ∀ g : G, ∫⁻ x, Φ (a x * g) ∂μ = ∫⁻ x, Φ (a x) ∂μ) →
    ∀ Ψ : G → ℂ, (∀ g : G, Integrable (fun x => Ψ (a x * g)) μ) → (∀ (p : P) (g : G), Ψ ((p : G) * g) = (δ p : ℂ) * Ψ g) →
    ∀ g : G, ∫ x, Ψ (a x * g) ∂μ = ∫ x, Ψ (a x) ∂μ := by
  intro G _ P X _ μ a δ H Ψ hint heq g
  have hint1 : Integrable (fun x => Ψ (a x)) μ := by simpa using hint 1
  have hre := integral_re (hint g)
  have hre1 := integral_re hint1
  have him := integral_im (hint g)
  have him1 := integral_im hint1
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hre hre1 him him1
  apply Complex.ext
  · rw [← hre, ← hre1]
    refine product_bound_of_factor_bounds P μ a δ H (fun y => (Ψ y).re) (fun y => ?_) (fun p y => ?_) g
    · simpa using (hint y).re
    · simp [heq]
  · rw [← him, ← him1]
    refine product_bound_of_factor_bounds P μ a δ H (fun y => (Ψ y).im) (fun y => ?_) (fun p y => ?_) g
    · simpa using (hint y).im
    · simp [heq]

end GlobalTheory
