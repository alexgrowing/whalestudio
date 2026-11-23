import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedFormDichotomy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interpolated_form_dichotomy : ∀ {n : Type} [Fintype n] {P₀ P : Matrix n n ℂ} {σ ρ N C₂ K : ℝ} {d ℓ : ℂ} {v X Y : n → ℂ}, P₀.PosDef → P.PosDef → 0 ≤ σ → σ ≤ 1 → 0 < ρ → 0 ≤ N → ℓ.im = 0 → ρ * (form P₀ v v).re ≤ (form P v v).re → ρ * (form P v v).re ≤ (form P₀ v v).re → gnorm P₀ Y ≤ C₂ * N * gnorm P₀ v → (∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X w = (σ : ℂ) * form P Y w + d * (form P v w - form P₀ v w)) → ((d = 0 ∧ ℓ.re = 0) ∨ (σ < 1 ∧ ‖d‖ ≤ K * (1 - σ) * N ∧ ‖d‖ ^ 2 ≤ K * N ^ 2 * σ * (σ + ρ * (1 - σ)) ∧ |ℓ.re| ≤ K * N ^ 2 * (σ + ρ * (1 - σ)) ∧ |ℓ.re| ≤ K * N ^ 2 * (1 - σ))) → |((form P₀ v v - form P v v) * ℓ - 2 * ((d * starRingEnd ℂ (form P Y v)).re : ℂ) + form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) X X - (σ : ℂ) * form P Y Y).re| ≤ (2 * C₂ ^ 2 + 4 * |K| + 3 * K ^ 2) * N ^ 2 * ((1 - σ) * (form P₀ v v).re + σ * (form P v v).re) := by
  first | exact @GlobalTheory.CurvRemainder.remainder_bound | exact GlobalTheory.CurvRemainder.remainder_bound | (intros; apply GlobalTheory.CurvRemainder.remainder_bound <;> assumption)
