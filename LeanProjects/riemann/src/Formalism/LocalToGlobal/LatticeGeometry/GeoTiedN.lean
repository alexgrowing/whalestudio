import Formalism.LocalToGlobal.LatticeGeometry.GeoTied

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)}
  {ng : NgPkg}

def NeatU {w : Dat D Lev} (U : ShimU D G jC ng w) : Prop :=
  ∀ (c : U.Comp) (γ : U.cx.Γ c), IsOfFinOrder γ → γ = 1

def GeoTiedMN (X : DivX D) : Prop :=
  ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
    TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC ∧
      (∀ w, NeatU (F.U w) → MumfordU (F.U w)) ∧ (∀ w, CurveHTDom (F.U w))

end Formalism.L2.Geo
