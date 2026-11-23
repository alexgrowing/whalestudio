import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_away_from_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), Function.Injective β → ∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → (∀ s, 𝔐.V s q = 𝔐.dR s q) ∧ (∀ p : ℕ, p.Prime → ∀ s, 𝔐.HT p s q = 𝔐.dR s q) ∧ 𝔐.M.lat q = ⨆ s, 𝔐.dR s q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero | exact GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero <;> assumption)
