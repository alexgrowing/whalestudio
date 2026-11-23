import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def overPrime (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) : Set (Cpt ξ) :=
  {q | ∀ p' : ℕ, p'.Prime → p' ≠ p → ¬ InFibre ξ p' q}

def IsLatFlagPair {E : Type} [AddCommGroup E] [Module Ω E] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type}
    (y : (Σ k, J k) → Ω) (T : Set (Cpt ξ)) (L L' : Lat ξ E) {r : ℕ} (b : Fin r → E) (Q : LocPair J ℤ (Fin r)) : Prop :=
  L.IsFlagVBOn T b ∧ L'.IsFlagVBOn T b ∧ ∀ i, ∃ e e' : Ω,
    (L.gr b i).IsDegOn T y (Q.x i) e ∧ (L'.gr b i).IsDegOn T y (Q.x' i) e' ∧
    (∃ bf bg : K → ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (Q.f i) bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (Q.g i) bg ∧ (fun k => (bf k : ℤ) - bg k) = Q.x i - Q.x' i) ∧
    aeval y (Q.g i) ≠ 0 ∧ aeval y (Q.f i) = e' / e * aeval y (Q.g i)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def IsFrobLabels (c : Coeff l) (p : ℕ) (φ : Equiv.Perm (CMType H ⊕ CMType H)) : Prop :=
  ∀ n : Ideal (𝓞 c.F), n.IsPrime → (p : 𝓞 c.F) ∈ n → ∀ s (a : 𝓞 E) (u v : 𝓞 c.F),
    (u : c.F) = labelEmb c (φ s) a → (v : c.F) = labelEmb c s a → u - v ^ p ∈ n

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

namespace HodgeCpt

def VAt (𝔐 : HodgeCpt Y S y) (S₀ : Finset ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li :=
  Lat.patch S₀ (𝔐.dR s) fun p => 𝔐.HT p s

def shrink (𝔐 : HodgeCpt Y S y) (S₀ : Finset ℕ) (h : S₀ ⊆ S)
    (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) : HodgeCpt Y S₀ y :=
  { 𝔐 with
    S_prime := fun p hp => 𝔐.S_prime p (h hp)
    R_ge := fun p hp => 𝔐.R_ge p (h hp)
    tors := fun p hp => 𝔐.tors p (h hp)
    vb := hvb }

def Flag.shrink {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S)
    (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s))
    (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) : (𝔐.shrink S₀ h hvb).Flag :=
  @Flag.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (𝔐.shrink S₀ h hvb) Fl.b hsub Fl.Li₀ Fl.acg Fl.mod Fl.M₀ Fl.j
    Fl.j_pt Fl.V₀ Fl.V₀_mem Fl.deg Fl.generic

abbrev constAlg (𝔐 : HodgeCpt Y S y) : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra

def Flag.TwoLevels [DecidableEq K] {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) (S₀ : Finset ℕ)
    (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))) : Prop :=
  ∃ (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s))
    (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (e₀ e : CMType H × Fin (D.p + D.q) → Ω),
    (Fl.shrink S₀ h hvb hsub).RootLines T.x e₀ ∧ Fl.RootLines T.x' e ∧
    (∀ r, aeval y (T.f r) = e r / e₀ r * aeval y (T.g r)) ∧
    T.IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn)

def wholeW (𝔐 : HodgeCpt Y S y) (n : ℕ) : Lat 𝔐.ξ 𝔐.Li := fun q =>
  Submodule.span (regAt 𝔐.ξ q) {e | ∀ w ∈ 𝔐.M.htOm 𝔐.t.PP.L n q, w e ∈ regAt 𝔐.ξ q}

end HodgeCpt

end

end GlobalTheory.CompanionTheory.Ar
