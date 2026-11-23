import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

def IsCp {Ω : Type} [CommRing Ω] (p : ℕ) (κ : Ω) : Prop :=
  if p = 2 then κ = 4 else ∃ ζ : Ω, IsPrimitiveRoot ζ p ∧ κ = ζ - 1

abbrev cmConj (E : Type) [Field E] [NumberField E] [IsCMField E] : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

abbrev omP (p : ℕ) : Lat 𝔐.ξ (Module.Dual Ω 𝔐.Li) := 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)

def HTFree (p : ℕ) : Prop :=
  (omP 𝔐 p).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((omP 𝔐 p).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q} (labelRk D s) ⊤

def OverZp (p : ℕ) (q : Cpt 𝔐.ξ) : Prop := ∀ r : ℕ, r.Prime → InFibre 𝔐.ξ r q → r = p

structure IsHTFamily (p : ℕ) (o : Type) [CommRing o] [Algebra o Ω]
    (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)) : Prop where
  act : ∀ s (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), (Dc s).ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)
  e_eq : ∀ s t, (Dc s).e = (Dc t).e
  om_iff : ∀ s w, w ∈ (Dc s).om ↔ ∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q
  om_loc : ∀ s q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q →
    𝔐.M.omLat q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om : Set (Module.Dual Ω 𝔐.Li))
  om'_loc : ∀ s q, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q →
    omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om' : Set (Module.Dual Ω 𝔐.Li))
  glue : ∀ s t q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q →
    ∀ x, ∃ w ∈ 𝔐.M.omLat q, (Dc s).h x = (Dc t).h x + (p ^ 𝔐.R p) • w

def Sandwich (p : ℕ) (κ : Ω) : Prop :=
  ∀ q, InFibre 𝔐.ξ p q → κ ∈ regAt 𝔐.ξ q ∧ omP 𝔐 p q ≤ 𝔐.M.omLat q ∧ (∀ w ∈ 𝔐.M.omLat q, κ • w ∈ omP 𝔐 p q) ∧
    ∀ s, 𝔐.dR s q ≤ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q ∧
      ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q, κ • e ∈ 𝔐.dR s q

end GlobalTheory.CompanionTheory.Ar.HT
