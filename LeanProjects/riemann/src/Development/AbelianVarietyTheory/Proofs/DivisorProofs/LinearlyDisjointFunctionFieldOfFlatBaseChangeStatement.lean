import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointFunctionFieldOfFlatBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D), a.Flat → ∀ (H : Over (Sp T)) [IsIntegral H.left] (H' : Over (Sp D)) [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  first | exact @GlobalTheory.Desc.FlatLin.linDisj_of_flat | exact GlobalTheory.Desc.FlatLin.linDisj_of_flat | (intros; apply GlobalTheory.Desc.FlatLin.linDisj_of_flat <;> assumption)
