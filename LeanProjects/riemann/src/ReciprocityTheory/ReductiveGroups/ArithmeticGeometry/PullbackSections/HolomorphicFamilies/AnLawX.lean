import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartX

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField

section Chart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} [Algebra c.F ℂ]

theorem anX_law_chart (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
    (hPair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (F.ex i P (anPr 0 v)).left (F.ex i P (anPr 1 v)).left
        ((Over.w (F.ex i P (anPr 0 v))).trans (Over.w (F.ex i P (anPr 1 v))).symm)) (m : ℕ) :
    homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ anX F i P hP y hy m =
      jpt y g (anX F i P hP y hy) m (0 : Fin 2) * jpt y g (anX F i P hP y hy) m (1 : Fin 2) :=
  jets_law y.x (F.ex i P) (anHol F i P hP) (anX F i P hP y hy) (fun _ => rfl) (F.ex_add i P hP) hPair m

end Chart

end ReciprocityTheory.ChartRestriction.G.PullbackSections
