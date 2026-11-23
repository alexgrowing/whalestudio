import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointComp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField), PFF (𝟙 _) π θ → ∀ (y : Y) (u : X.functionField), GlobalTheory.Cartier.RegAt (π y) u → GlobalTheory.Cartier.RegAt y (θ u) := by
  first | exact @GlobalTheory.Desc.RegPull.regAt_map | exact GlobalTheory.Desc.RegPull.regAt_map | (intros; apply GlobalTheory.Desc.RegPull.regAt_map <;> assumption)
