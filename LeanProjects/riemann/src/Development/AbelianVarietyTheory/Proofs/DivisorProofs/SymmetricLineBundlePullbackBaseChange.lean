import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymBaseChange

theorem inv_left_fst (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) :
    (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left ≫ pullback.fst G.hom j =
      pullback.fst G.hom j ≫ (GrpObj.inv : G ⟶ G).left := by
  exact pullback.lift_fst _ _ _

theorem symm_pull : ∀ (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) (L : LB G.left), L.IsLB → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso ((L.pull (pullback.fst G.hom j)).pull (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left) (L.pull (pullback.fst G.hom j)) := by
  intro S T G _ j L hL h
  have e := inv_left_fst S T G j
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom j) (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom j) e
  have h3 := GenSpread.lbIso_pullback h (pullback.fst G.hom j)
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymBaseChange
