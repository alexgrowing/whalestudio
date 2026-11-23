import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisibilityOnClosedFibreSpreads
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibility_on_closed_fibre_spreads : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R →
    ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ (r : R), r ≠ 0 → ∀ (W : G.left.Opens) (a : Γ(G.left, W))
    (x : G.left), x ∈ W → (∀ y ∈ W, (∃ z : G.left, G.hom z = closedPoint R ∧ y ⤳ z) → cst G.hom y r ∣ gs (𝟙 G.left) y W a) →
    cst G.hom x r ∣ gs (𝟙 G.left) x W a := by
  first | exact @GlobalTheory.Spread.dvd_of_dvd_near_closedFibre | exact GlobalTheory.Spread.dvd_of_dvd_near_closedFibre | (intros; apply GlobalTheory.Spread.dvd_of_dvd_near_closedFibre <;> assumption)
