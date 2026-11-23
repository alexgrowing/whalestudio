import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def EmbedsGeneric {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type}
    (x : κ → Ω) : Prop :=
  ∀ p : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → (∃ i, InChart ξ x i p) ∧ ∀ i, InChart ξ x i p →
    (∀ a ∈ regAt ξ p, ∃ s ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i), unitAt ξ p s ∧
      s * a ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i)) ∧
    ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → InChart ξ x i q →
      (∀ s ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i), unitAt ξ p s ↔ unitAt ξ q s) → p = q

structure RefGeo (Y : Model Xo c β) where

  Ω : Type
  [fld : Field Ω]
  [cz : CharZero Ω]

  K : Type
  [finK : Fintype K]

  J : K → Type
  [finJ : ∀ k, Fintype (J k)]

  y : (Σ k, J k) → Ω

  𝔐 : HodgeCpt Y ∅ y

  Fl : 𝔐.Flag
  deg_one : Fl.deg = 1

  xdeg : RootIx D → K → ℤ

  e : RootIx D → Ω
  lines : Fl.RootLines xdeg e

  bd : Ideal (MRing J)
  snc : Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd
  bd_iff : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)

  k₀ : K
  embeds : EmbedsGeneric 𝔐.ξ fun i : J k₀ => y ⟨k₀, i⟩

attribute [instance] RefGeo.fld RefGeo.cz RefGeo.finK RefGeo.finJ

structure RefGeo.An {Y : Model Xo c β} (G : RefGeo Y) where

  sing : RootIx D → HermLine G.J
  sing_deg : ∀ r, (sing r).a = G.xdeg r
  hodge : ∀ r, G.Fl.IsHodgeLine r (G.e r) (sing r)

  Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))

  Re : PB.Realis Sys (mCoordIdeal G.y)
  J_top : Re.J = ⊤
  deg_one : Re.deg = 1
  π_bij : Function.Bijective Re.π
  embedded : Cmp.IsEmbedded Re.R.A (mCoordIdeal G.y) Re.R.U Re.R.lift
  interior : ∀ x (z : Spec (CommRingCat.of ℂ) ⟶ G.𝔐.X), CoordsAt G.𝔐.ξ G.y z (Re.R.lift x x) →
    (G.𝔐.Interior z ↔ Re.π x ∈ Sys.open')
  fund_deg : ∀ τ i, (Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, G.xdeg (τ, k)
  fund_sing : ∀ τ i x, Re.π x ∈ Sys.open' →
    Real.log ((Re.ref (some (τ, i))).h (Re.R.lift x x)) + Sys.ph (some (τ, i)) (Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (Re.R.lift x x))
  conj : ∀ a t, IsSmoothHerm (Re.line a t) ∧ IsConjInvariantH (Re.line a t)
  none_deg : (Re.ref none).a G.k₀ = 1 ∧ ∀ k, k ≠ G.k₀ → (Re.ref none).a k = 0
  none_h : ∀ z, (Re.ref none).h z = Real.sqrt (∑ i, ‖z ⟨G.k₀, i⟩‖ ^ 2)
  pos : ReciprocityTheory.AnForm.M.IsPosPot Sys.A (Sys.th none)
  ph_none : ∀ x, Sys.ph none x = 0 ∧ ∀ t, Sys.phT none t x = 0
  flat : ∀ τ (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q → ∀ t,
    ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, i)) t).rsmul (-1)) ∧
      ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, i)) t)

def RefGeo.IsEff {Y : Model Xo c β} (G : RefGeo Y) (n : RootIx D → ℤ) (q' : ℕ) (s : G.Ω) : Prop :=
  ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → ∀ (i : G.J G.k₀) (t : G.Ω),
    InChart G.𝔐.ξ (fun i' : G.J G.k₀ => G.y ⟨G.k₀, i'⟩) i p → (Lat.tens G.Fl.rootLat fun r => -n r).IsGenAt p t →
      s * G.y ⟨G.k₀, i⟩ ^ q' / t ∈ regAt G.𝔐.ξ p ∧
        (p.1 ∉ abLocus G.𝔐.t.G → ¬ unitAt G.𝔐.ξ p (s * G.y ⟨G.k₀, i⟩ ^ q' / t))

end GlobalTheory.CompanionTheory.Ar
