import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

namespace GlobalTheory.ChainPts

theorem coef_dual (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (V V' : X.Opens) (e : Fin r → Γ(F, V))
    (s : Fin r → Γ(F, V')) (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r) :
    GlobalTheory.ChainPts.coef true he.dual hs.dual l i = GlobalTheory.ChainPts.coef false he hs l i := by
  change (hs.dual.basis inf_le_right).repr (GlobalTheory.Twist.resM (GlobalTheory.VB.dual F) inf_le_left (he.coord l)) i =
    (he.basis inf_le_left).repr (GlobalTheory.Twist.resM F inf_le_right (s i)) l
  rw [GlobalTheory.VB.IsFrame.dual_basis_repr, GlobalTheory.VB.dualApp_res, GlobalTheory.VB.IsFrame.dualApp_coord]

end GlobalTheory.ChainPts
