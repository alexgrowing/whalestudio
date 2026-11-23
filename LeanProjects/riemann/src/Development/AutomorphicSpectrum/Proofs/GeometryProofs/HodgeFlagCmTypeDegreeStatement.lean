import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagCmTypeDegree
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_flag_cm_type_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] [DecidableEq (CMType H)] (Fl : 𝔐.Flag)
    (S₀ : Finset ℕ) (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))), Fl.TwoLevels S₀ T → ∀ p ∈ S, p ∉ S₀ →
    (∀ (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) → 𝔐.HT p s q = 𝔐.dR s q) →
    ∀ s, IsLatFlagPair y (overPrime 𝔐.ξ p) (𝔐.dR s) (𝔐.HT p s) (Fl.b s) (labelPair D T s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwoLevelLat.latFlagPair_of_twoLevels | exact GlobalTheory.CompanionTheory.Ar.TwoLevelLat.latFlagPair_of_twoLevels | (intros; apply GlobalTheory.CompanionTheory.Ar.TwoLevelLat.latFlagPair_of_twoLevels <;> assumption)
