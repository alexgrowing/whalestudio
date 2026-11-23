import Formalism.LocalToGlobal.ProjectiveLattices.IsExpChart

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def ExpBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S')
    (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' →
    ∀ (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) (e : ∀ m, ExpFr y x m), IsExpChart y x → IsExpGauge y x e →
    ∃ (x' : ∀ m, jO y' (dL Dw) m 1 ⟶ Xo.univ.t.G) (e' : ∀ m, ExpFr y' x' m),
      IsExpChart y' x' ∧ IsExpGauge y' x' e' ∧
      ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom →
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y'.x))) (g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
        IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' →
        IsExpGerm y x e k F g → IsExpGerm y' x' e' k F' (MvPowerSeries.map ψ.toRingHom g)

end Formalism.L2.Pj
