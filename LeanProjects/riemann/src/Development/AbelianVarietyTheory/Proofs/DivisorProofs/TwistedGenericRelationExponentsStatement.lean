import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGenericRelationExponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_generic_relation_exponents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (n n' : Letter Dw → ℤ), TriEqn C → T.LocRel C C' φ ψ t₀ → C.Y.dim = C'.Y.dim → (∀ z, n' (T.letter z) = n z) → DivIso (divOf C n') (divOf C' n) φ ψ (prodPow t₀ n) := by
  first | exact @GlobalTheory.ShFam.GalCarry.divIso_divOf_of_locRel | exact GlobalTheory.ShFam.GalCarry.divIso_divOf_of_locRel | (intros; apply GlobalTheory.ShFam.GalCarry.divIso_divOf_of_locRel <;> assumption)
