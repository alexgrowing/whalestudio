import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointCompStructureEqSpecMapConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R), gp X ≫ p = spMap (cst p) := by
  first | exact @GlobalTheory.Desc.gp_comp_eq_spMap_cst | exact GlobalTheory.Desc.gp_comp_eq_spMap_cst | (intros; apply GlobalTheory.Desc.gp_comp_eq_spMap_cst <;> assumption)
