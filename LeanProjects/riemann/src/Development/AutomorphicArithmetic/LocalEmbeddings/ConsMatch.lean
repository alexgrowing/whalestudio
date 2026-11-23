import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam
open GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm (IsOver PullsBack)

namespace GlobalTheory.ConsGeo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {O : Type} [CommRing O] {β : O →+* i₀.c.F}

def incl (Z : Mdl Y i₀) : i₀.c.F →+* Z.i.c.F := (IntermediateField.inclusion Z.le).toRingHom

structure Lev (Z : Mdl Y i₀) (T : Model (Xo i₀.l) i₀.c β) : Type where

  r : (Xo Z.i.l).XF Z.i.c ⟶ (Xo i₀.l).XF i₀.c

  ν : SABMap (Y Z.i).oF.t T.oF.t r

  snd : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (incl Z)

  fst : ∃ π : (Xo Z.i.l).X ⟶ (Xo i₀.l).X, IsOver Z.dvd _ _ π ∧ PullsBack _ _ π ∧
    r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π

variable {Z : Mdl Y i₀} {T : Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F}

def Match (L : Lev Z T) (C : FlagCpt T e) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (q : Sp k ⟶ C.Y.X) : Prop :=
  ∃ (y : Sp k ⟶ (Xo Z.i.l).XF Z.i.c) (v : Vecs Dw (Y Z.i).oF.t k) (φ : i₀.c.F →+* k)
    (g : EigFrame T φ (q ≫ C.π ≫ genι T)),
    w ≫ Z.π = y ≫ (Y Z.i).j ∧ q ≫ C.π = y ≫ L.r ≫ T.jQ ∧ (∀ τ i, IsTanAtG (Y Z.i).oF.t y (v τ i)) ∧
      Z.FlagAt w (fun τ i => v τ i ≫ (Y Z.i).m.φ) ∧ C.Carries q g ∧ ∀ τ i, g.v τ i = v τ i ≫ L.ν.φ ≫ T.m.φ

end GlobalTheory.ConsGeo

end
