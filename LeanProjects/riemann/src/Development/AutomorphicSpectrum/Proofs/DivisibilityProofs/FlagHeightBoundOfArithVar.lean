import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticesPrimeCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagHeightBoundArithVarStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem rootLines_vert_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (x x' : CMType H × Fin (D.p + D.q) → K → ℤ) (e₀ e : CMType H × Fin (D.p + D.q) → Ω), (Fl.shrink S₀ h hvb hsub).RootLines x e₀ → Fl.RootLines x' e → ∃ f g : CMType H × Fin (D.p + D.q) → MvPolynomial (Σ k, J k) ℤ, (∀ r, aeval y (f r) = e r / e₀ r * aeval y (g r)) ∧ (⟨x, x', f, g⟩ : LocPair J ℤ (CMType H × Fin (D.p + D.q))).IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d ha Fl S₀ h hvb hsub x x' e₀ e h₀ h₁
  have key : ∀ r, ∃ f g : MvPolynomial (Σ k, J k) ℤ,
      (⟨fun _ => x r, fun _ => x' r, fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y)
        ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧
      aeval y f = e r / e₀ r * aeval y g := by
    intro r
    refine GlobalTheory.T.degree_lattices_prime_compare 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d ha ((Fl.shrink S₀ h hvb hsub).rootLat r) (Fl.rootLat r)
      (x r) (x' r) (e₀ r) (e r) (h₀ r) (h₁ r) _ ?_
    intro q hq
    exact GlobalTheory.T.flag_height_bound_arith_var E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha Fl S₀ h hvb hsub q
      (fun p hp hp' hf => hq ⟨p, 𝔐.S_prime p hp⟩ (Finset.mem_preimage.2 (Finset.mem_sdiff.2 ⟨hp, hp'⟩)) hf) r
  choose f g hv hr using key
  exact ⟨f, g, hr, fun r => hv r ()⟩

end GlobalTheory.CompanionTheory.Ar.Num
