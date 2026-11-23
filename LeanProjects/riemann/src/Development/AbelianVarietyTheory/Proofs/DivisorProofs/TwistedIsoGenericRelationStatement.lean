import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedIsoGenericRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_iso_generic_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X), (∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ C.Y.X), T.PtRel C C' p (p ≫ φ.hom)) → ∃ (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), T.GenRel C C' φ ψ t₀ := by
  first | exact @GlobalTheory.ShFam.GalCarry.Tw.exists_genRel | exact GlobalTheory.ShFam.GalCarry.Tw.exists_genRel | (intros; apply GlobalTheory.ShFam.GalCarry.Tw.exists_genRel <;> assumption)
