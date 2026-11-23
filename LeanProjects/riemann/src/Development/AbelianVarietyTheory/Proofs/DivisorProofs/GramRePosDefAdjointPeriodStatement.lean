import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramRePosDefAdjointPeriod
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_re_posDef_adjoint_period : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (P : D.La →+ (Fin g → ℂ)) (r : ℕ) (e : Module.Basis (Fin r) ℤ D.La), IsPeriod D ρ P → ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.IsHermitian ∧ (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) ∧ ∀ a : O, Q * actM D e ℂ (bar a) = (actM D e ℂ a)ᴴ * Q := by
  first | exact @GlobalTheory.PELU.gram_re_posdef_adj | exact GlobalTheory.PELU.gram_re_posdef_adj | (intros; apply GlobalTheory.PELU.gram_re_posdef_adj <;> assumption)
