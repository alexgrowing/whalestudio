import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonempty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCharZeroGenericModel_nonempty : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (GenModel gb N) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.genModel_nonempty) | (exact GlobalTheory.UPel.HT.Gen.genModel_nonempty) | (intros; apply GlobalTheory.UPel.HT.Gen.genModel_nonempty  <;> assumption)
