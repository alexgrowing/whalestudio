import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesCurveMulCoprime
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixesCurve_mul_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (m n p : ℕ) (A : ValuationSubring ℂ) (τ : ℂ ≃+* ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ¬ p ∣ n → Nat.Coprime m n → 3 ≤ m / p ^ m.factorization p → FixesCurve H τ m → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → FixesCurve H τ (m * n) := by
  first | exact @GlobalTheory.CompRat.Inertia.fixesCurve_mul | exact GlobalTheory.CompRat.Inertia.fixesCurve_mul | (intros; apply GlobalTheory.CompRat.Inertia.fixesCurve_mul <;> assumption)
