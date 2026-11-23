import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O

def Setup.DualRef {D : D7} (O : Setup D) : Prop :=
  ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (x : DV.Rt D.what₂.Tau O.N) (z : Pts (O.var c) σ) (f : (O.var c).Fn),
    (divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under z) f →
      (cxSt _).pn _ σ _ (O.met.h0 c σ (O.ex x)) ((cxSt _).cx _ σ f) z *
        (cxSt _).pn _ σ _ (O.met.h0 c σ (-O.ex x)) ((cxSt _).cx _ σ f⁻¹) z = 1

end GlobalTheory.Mean4O
