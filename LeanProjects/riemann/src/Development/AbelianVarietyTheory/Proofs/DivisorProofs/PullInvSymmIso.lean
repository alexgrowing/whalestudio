import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLB

theorem pull_inv_symm_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → LBIso ((LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]).pull (GrpObj.inv : G ⟶ G).left) (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]) := by
  intro S G _ L hL
  have h₁ := LB.isLB_linComb hL (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB h₁ _) h₁).1 ?_
  rw [GlobalTheory.CechPic.cls_pull h₁, GlobalTheory.CechPic.cls_linComb hL _ _ h₁]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add,
    ← GlobalTheory.CechPic.pull_comp]
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left, Category.comp_id, add_comm]

end GlobalTheory.SymLB
