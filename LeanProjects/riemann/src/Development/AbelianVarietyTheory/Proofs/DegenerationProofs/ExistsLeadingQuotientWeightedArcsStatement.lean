import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLeadingQuotientWeightedArcs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leading_quotient_weighted_arcs : ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  first | exact @GlobalTheory.SS.exists_polynomial_leading_quotient_subst | exact GlobalTheory.SS.exists_polynomial_leading_quotient_subst | (intros; apply GlobalTheory.SS.exists_polynomial_leading_quotient_subst <;> assumption)
