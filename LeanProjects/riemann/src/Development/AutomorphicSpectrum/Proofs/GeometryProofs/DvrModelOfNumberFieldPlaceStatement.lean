import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_model_of_number_field_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (v : HeightOneSpectrum (𝓞 F')) (π : F'), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → NormalCpt ξ → v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra O Ω) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (s : X' ⟶ Spec (CommRingCat.of O)) (g : X' ⟶ X) (ϖ : O), IsProper s ∧ Irreducible ϖ ∧ Function.Injective (algebraMap O Ω) ∧ ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ∧ ξ' ≫ g = ξ ∧ IsCptGen ξ' ∧ (∀ q' : X', genPt ξ' ⤳ q') ∧ algebraMap O Ω ϖ = ψ π ∧ (∀ a : Ω, a ∈ (algebraMap O Ω).range ↔ ∃ b : F', v.valuation F' b ≤ 1 ∧ ψ b = a) ∧ (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → ∃ p' : Cpt ξ', g p'.1 = p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | exact GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation <;> assumption)
