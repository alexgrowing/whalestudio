import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeTransportEquiv
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_transport_equiv : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport <;> assumption)
