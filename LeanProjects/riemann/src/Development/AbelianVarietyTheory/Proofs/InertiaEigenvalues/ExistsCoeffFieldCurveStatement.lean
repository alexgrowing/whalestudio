import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldCurve
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_field_curve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l l₂ : Level H) (c : Coeff l) (n p : ℕ), p.Prime → ¬ p ∣ n → Nat.Coprime l.M n → l₂.M = l.M * n → l₂.A = 1 → l.GoodAt p → CurveOver H c.F l.M → ∃ c' : Coeff l₂, c.F ≤ c'.F ∧ CurveOver H c'.F l₂.M ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c'.F, τ x ∈ c'.F) ∧ ∀ A : ValuationSubring ℂ, (p : ℂ) ∈ A.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → ∀ x ∈ c'.F, τ x = x := by
  first | exact @GlobalTheory.DeepCoeff.exists_coeff_unramified | exact GlobalTheory.DeepCoeff.exists_coeff_unramified | (intros; apply GlobalTheory.DeepCoeff.exists_coeff_unramified <;> assumption)
