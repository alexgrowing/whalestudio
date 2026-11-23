import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPointRelationFieldExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_point_relation_field_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (K K' : Type) [Field K] [Field K'] (ν : K →+* K') (p : Sp K ⟶ C.Y.X) (p' : Sp K ⟶ C'.Y.X), T.PtRel C C' p p' → T.PtRel C C' (spMap ν ≫ p) (spMap ν ≫ p') := by
  first | exact @GlobalTheory.ptRel_map | exact GlobalTheory.ptRel_map | (intros; apply GlobalTheory.ptRel_map <;> assumption)
