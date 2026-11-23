import Formalism.LocalToGlobal.LatticeGeometry.Inhabited

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField

namespace Formalism.L2.Geo

variable {D : D7}

def GeoTied (X : DivX D) : Prop :=
  ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
    TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC

def GeoTiedM (X : DivX D) : Prop :=
  ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
    TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC ∧
      (∀ w, MumfordU (F.U w)) ∧ (∀ w, CurveHTDom (F.U w))

end Formalism.L2.Geo
