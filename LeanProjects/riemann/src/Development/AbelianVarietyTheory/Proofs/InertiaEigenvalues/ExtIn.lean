import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTransfer

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def ExtIn (Y : Model Xo c β) (S : Set Y.X) (T : CDVR) (io : c.F →+* T.Fr) (x : Sp T.Fr ⟶ Xo.X) : Prop :=
  ∃ (y' : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), z ≫ pullback.fst _ _ = x ∧ z ≫ pullback.snd _ _ = spMap io ∧
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' ∧ Set.range y' ⊆ S

theorem ExtIn.mono {Y : Model Xo c β} {S S' : Set Y.X} (h : S ⊆ S') {T : CDVR} {io : c.F →+* T.Fr}
    {x : Sp T.Fr ⟶ Xo.X} (hx : ExtIn Y S T io x) : ExtIn Y S' T io x := by
  obtain ⟨y', z, h1, h2, h3, h4⟩ := hx
  exact ⟨y', z, h1, h2, h3, h4.trans h⟩

end GlobalTheory.GoodTransfer
