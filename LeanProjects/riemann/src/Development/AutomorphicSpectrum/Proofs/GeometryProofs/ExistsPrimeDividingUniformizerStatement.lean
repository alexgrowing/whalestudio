import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizer
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_dividing_uniformizer : ∀ (F' : Type) [Field F'] [NumberField F'] (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | exact GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | (intros; apply GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser <;> assumption)
