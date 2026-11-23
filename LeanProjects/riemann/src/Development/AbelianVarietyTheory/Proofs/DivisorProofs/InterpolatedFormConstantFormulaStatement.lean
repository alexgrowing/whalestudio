import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedFormConstantFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interpolated_form_constant_formula : ∀ {n : Type} [Fintype n] {P₀ P : Matrix n n ℂ} (σ : ℝ) {θ₀ θ θs : Matrix n n ℂ} {d ℓ Φ₀ Φ Φs D₀ D Ds : ℂ} {v : n → ℂ}, P₀.IsHermitian → P.IsHermitian → Φ₀ = form P₀ (θ₀ *ᵥ v) (θ₀ *ᵥ v) - D₀ → Φ = form P (θ *ᵥ v) (θ *ᵥ v) - D → Φs = form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) (θs *ᵥ v) (θs *ᵥ v) - Ds → Ds = ((1 - σ : ℝ) : ℂ) * D₀ + (σ : ℂ) * D + (form P v v - form P₀ v v) * ℓ + d * (form P v (θ *ᵥ v) - form P₀ v (θ₀ *ᵥ v)) + starRingEnd ℂ d * (form P (θ *ᵥ v) v - form P₀ (θ₀ *ᵥ v) v) → (∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) ((θs - θ₀) *ᵥ v) w = (σ : ℂ) * form P ((θ - θ₀) *ᵥ v) w + d * (form P v w - form P₀ v w)) → Φs = ((1 - σ : ℝ) : ℂ) * Φ₀ + (σ : ℂ) * Φ + ((form P₀ v v - form P v v) * ℓ - 2 * ((d * starRingEnd ℂ (form P ((θ - θ₀) *ᵥ v) v)).re : ℂ) + form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) ((θs - θ₀) *ᵥ v) ((θs - θ₀) *ᵥ v) - (σ : ℂ) * form P ((θ - θ₀) *ᵥ v) ((θ - θ₀) *ᵥ v)) := by
  first | exact @GlobalTheory.curvature_term_algebra | exact GlobalTheory.curvature_term_algebra | (intros; apply GlobalTheory.curvature_term_algebra <;> assumption)
