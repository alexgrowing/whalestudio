import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupAlgebraActionOfCommuteOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupAlgebra_action_of_commute_order : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) → ∃ y, actOn L.rep (AfP p) y = A := by
  first | (exact @GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (exact GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (intros; apply GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute  <;> assumption)
