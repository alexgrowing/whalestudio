import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal)

def HodgeLatticeFlagBoundAllPlaces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ p ∈ S, HT.HTFree 𝔐 p → ∀ (g : ℕ), Module.finrank Ω 𝔐.Li = g → ∀ (b : Fin g → 𝔐.Li) (b' : Fin g → Module.Dual Ω 𝔐.Li)
      (lie om : LocPair J ℤ (Fin g)),
      IsLatFlagPair y (overPrime 𝔐.ξ p) 𝔐.M.lat (𝔐.wholeW (p ^ 𝔐.R p)) b lie →
      IsLatFlagPair y (overPrime 𝔐.ξ p) 𝔐.M.omLat (𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)) b' om →
      ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ =>
        BundleChernComparison (pointIdeal O y) d p (lie.map (Int.castRingHom O)) (om.map (Int.castRingHom O))

end GlobalTheory.CompanionTheory.Ar
