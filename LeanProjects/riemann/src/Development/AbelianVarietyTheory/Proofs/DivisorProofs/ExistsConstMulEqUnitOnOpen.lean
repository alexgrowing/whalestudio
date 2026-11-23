import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToStkACv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX GlobalTheory.MBEx
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.OpenPartUnit

section General

variable {X Y Y' G B Z : Scheme.{0}}

theorem gs_appLE (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (h : r z ∈ W)
    (a : Γ(X, U)) : gs r z W ((f.appLE U W e).hom a) = gs (r ≫ f) z U a :=
  (gs_res r z e h _).trans (gs_pull r f z U (e h) a)

end General

end GlobalTheory.OpenPartUnit
