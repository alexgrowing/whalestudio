import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLineClassFlagDeterminantExpansion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelExpNonneg
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_line_class_flag_determinant_expansion : ∀ (ι : Type) [Fintype ι] (N : ℕ) (lam : ι → Fin N → ℤ), ∃ e₀ e₁ : ι → ℤ, (wtLine lam).icls = ∑ x : ι × Fin (N + 1), abelExp lam x • (flDet x.1 x.2 : GlobalTheory.HermLB (flStr ι N)).icls + ∑ τ, (e₀ τ • (flDet τ 0 : GlobalTheory.HermLB (flStr ι N)).icls + e₁ τ • (flDet τ (Fin.last N) : GlobalTheory.HermLB (flStr ι N)).icls) := by
  first | exact @GlobalTheory.FlagZ.AbelSum.icls_wtLine_eq_abel | exact GlobalTheory.FlagZ.AbelSum.icls_wtLine_eq_abel | (intros; apply GlobalTheory.FlagZ.AbelSum.icls_wtLine_eq_abel <;> assumption)
