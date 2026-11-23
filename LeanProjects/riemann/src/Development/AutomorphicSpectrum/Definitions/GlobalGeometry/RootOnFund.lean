import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open AlgebraicGeometry CategoryTheory NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def rootOnFund {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (r a : Ψ × Fin N) : ℤ :=
  if a.1 = r.1 then (if (a.2 : ℕ) + 1 = r.2 then 1 else 0) - (if a.2 = r.2 then 1 else 0) else 0

def fundOnRoot {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (a r : Ψ × Fin N) : ℤ :=
  if r.1 = a.1 ∧ r.2 ≤ a.2 then -1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

open Classical in

structure HodgeTie (Y : Model Xo c β) (S : Finset ℕ) (n : ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) where

  A : HodgeCpt Y S M.y

  Fl : A.Flag

  e : CMType H × Fin (D.p + D.q) → M.Ω
  roots : Fl.RootLines M.xdeg e

  sing : CMType H × Fin (D.p + D.q) → HermLine M.ι
  sing_deg : ∀ r, (sing r).a = M.xdeg r
  hodge : ∀ r, Fl.IsHodgeLine r (e r) (sing r)

  Sy : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (CMType H × Fin (D.p + D.q))

  Re : PB.Realis Sy M.P
  alg : AlgOver Re
  ref_deg : ∀ a, (Re.ref a).a = (Top.combLine sing (fundOnRoot a)).a
  sing_eq : ∀ a x, Re.π x ∉ ReciprocityTheory.AnForm.P.bdry Sy.s →
    Real.log ((Top.combLine sing (fundOnRoot a)).h (Re.R.lift x x)) =
      Real.log ((Re.ref a).h (Re.R.lift x x)) + Sy.ph a (Re.π x)
  line_eq : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ r, ∀ z ∈ mcPts M.P,
    (M.x t r).h z = (Top.combLine (fun a => Re.line a t) (rootOnFund r)).h z
  δ_eq : M.δ = n * Fl.deg
  discr : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S
  ht_vb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn
    {q | InFibre A.ξ p q} (labelRk D s) ⊤

def IsImageCpt {Y : Model Xo c β} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K]
    [Fintype K'] {J : K → Type} {J' : K' → Type} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (Φ : Xo.X ≅ Xo.X) (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') : Prop :=
  ∃ (x : Sp A.Ω₀ ⟶ Xo.XF c) (x' : Sp A'.Ω₀ ⟶ Xo.XF c) (ψ : A'.Ω₀ ≃+* A.Ω₀),
    A.ξ₀ = x ≫ Y.j ∧ A'.ξ₀ = x' ≫ Y.j ∧
    spMap ψ.toRingHom ≫ x' ≫ Limits.pullback.fst _ _ = x ≫ Limits.pullback.fst _ _ ≫ Φ.hom ∧
    spMap ψ.toRingHom ≫ x' ≫ Limits.pullback.snd _ _ = x ≫ Limits.pullback.snd _ _ ∧
    spMap A.fn ≫ x ≫ Limits.pullback.snd _ _ = spMap A.cst ∧
    spMap A'.fn ≫ x' ≫ Limits.pullback.snd _ _ = spMap A'.cst

end GlobalTheory.CompanionTheory.Ar.Cmp
