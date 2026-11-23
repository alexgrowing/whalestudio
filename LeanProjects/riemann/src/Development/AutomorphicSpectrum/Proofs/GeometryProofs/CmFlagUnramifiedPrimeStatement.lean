import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmFlagUnramifiedPrime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_flag_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q) → ∀ t : CMType H ⊕ CMType H, (𝔐.dR t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) ∧ (𝔐.HT p t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.hodgeLattices_isVBOn_overPrime | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.hodgeLattices_isVBOn_overPrime | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.hodgeLattices_isVBOn_overPrime <;> assumption)
