import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationValuationExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_relation_valuation_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] (ν : V →+* L) (k : Type) [Field k] (r : V →+* k) (q : Sp V ⟶ C.Y.X) (q' : Sp V ⟶ C'.Y.X), Function.Injective ν → RingHom.ker r = IsLocalRing.maximalIdeal V → T.PtRel C C' (spMap ν ≫ q) (spMap ν ≫ q') → T.PtRel C C' (spMap r ≫ q) (spMap r ≫ q') := by
  first | exact @GlobalTheory.ShFam.GalCarry.ptRel_spec | exact GlobalTheory.ShFam.GalCarry.ptRel_spec | (intros; apply GlobalTheory.ShFam.GalCarry.ptRel_spec <;> assumption)
