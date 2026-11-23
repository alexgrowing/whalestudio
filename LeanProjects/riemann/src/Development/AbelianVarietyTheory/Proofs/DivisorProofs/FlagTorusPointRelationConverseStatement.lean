import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusPointRelationConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_torus_point_relation_converse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (K : Type) [Field K] [IsAlgClosed K] (i' : U.Comp) (p' : Sp K ⟶ (Φ.C i').Y.X), ∃! q : Σ i : U.Comp, (Sp K ⟶ (Φ.C i).Y.X), T.PtRel (Φ.C q.1) (Φ.C i') q.2 p' := by
  first | exact @GlobalTheory.ShFam.GalCarry.RelBwd.existsUnique_source | exact GlobalTheory.ShFam.GalCarry.RelBwd.existsUnique_source | (intros; apply GlobalTheory.ShFam.GalCarry.RelBwd.existsUnique_source <;> assumption)
