import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

def e8LB {S : Scheme.{0}} (G₀ : Over S) [GrpObj G₀] (L : LB G₀.left) (W : Matrix (Fin 8) (Fin 8) ℤ) :
    LB (powObj G₀ 8).left :=
  LB.LinComb L (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))

end GlobalTheory.PowE8
end
