import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRelationUnitSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_relation_unit_symmetric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), T.GenRel C C' φ ψ t₀ → T.LocRel C C' φ ψ t₀ := by
  first | exact @GlobalTheory.ShFam.GalCarry.Tw.locRel_of_genRel | exact GlobalTheory.ShFam.GalCarry.Tw.locRel_of_genRel | (intros; apply GlobalTheory.ShFam.GalCarry.Tw.locRel_of_genRel <;> assumption)
