import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombination
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ordQ_eq_ord_div_of_rational_combination : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ), φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  first | exact @GlobalTheory.FieldPair.exists_ordQ_eq_ord_div | exact GlobalTheory.FieldPair.exists_ordQ_eq_ord_div | (intros; apply GlobalTheory.FieldPair.exists_ordQ_eq_ord_div <;> assumption)
