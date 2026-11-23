import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_over_number_field_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (σ : F' →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), NormalCpt ξ → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → PtOver y ψ σ w → genPt ξ ⤳ centre z → ∀ a : F', ValAt ξ z (ψ a) (σ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LiesOver.valAt_cst | exact GlobalTheory.CompanionTheory.Ar.Flat.LiesOver.valAt_cst | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LiesOver.valAt_cst <;> assumption)
