import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderFaithfulLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_order_faithful_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), (∀ y : D.La, x • y = 0) → x = 0 := by
  first | exact @GlobalTheory.HTFaith.faithful | exact GlobalTheory.HTFaith.faithful | (intros; apply GlobalTheory.HTFaith.faithful <;> assumption)
