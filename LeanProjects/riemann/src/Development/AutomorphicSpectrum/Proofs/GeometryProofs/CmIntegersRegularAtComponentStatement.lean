import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmIntegersRegularAtComponent
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_integers_regular_at_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : E →+* Z.Ω), (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) →
    ∀ (q : Cpt (Z.ξ₀ ≫ Y.j)) (a : 𝓞 E), σ (a : E) ∈ regAt (Z.ξ₀ ≫ Y.j) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt <;> assumption)
