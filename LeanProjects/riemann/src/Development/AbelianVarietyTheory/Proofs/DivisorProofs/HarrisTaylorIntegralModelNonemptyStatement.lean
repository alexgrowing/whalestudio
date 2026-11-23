import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonempty
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorIntegralModel_nonempty : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N) := by
  first | (exact @GlobalTheory.UPel.HT.model_nonempty) | (exact GlobalTheory.UPel.HT.model_nonempty) | (intros; apply GlobalTheory.UPel.HT.model_nonempty  <;> assumption)
