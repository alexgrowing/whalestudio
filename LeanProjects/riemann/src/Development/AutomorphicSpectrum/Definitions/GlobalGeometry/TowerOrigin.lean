import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

abbrev RootIx (D : Datum H) : Type := CMType H × Fin (D.p + D.q)

structure FixedData (Y : Model Xo c β)
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) where

  Ωf : Type
  [fld : Field Ωf]

  ξf : Spec (CommRingCat.of Ωf) ⟶ Y.X

  Lif : Type
  [acg : AddCommGroup Lif]
  [mod : Module Ωf Lif]
  Mf : LieModel Y.t.G ξf Lif

  bf : ∀ s, Fin (labelRk D s) → Lif

  m : ℕ

  yf : Fin (m + 1) → Ωf
  generate : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) => yf ij.1 / yf ij.2) = ⊤

  hf : (Fin (m + 1) → ℂ) → ℝ

  kA : ℕ

  pt : Sys.X → Fin (m + 1) → ℂ
  pt_ne : ∀ x, pt x ≠ 0
  pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x'
  pos : ReciprocityTheory.AnForm.M.IsPosPot Sys.A (Sys.th none)
  ph_none : ∀ x, Sys.ph none x = 0 ∧ ∀ t, Sys.phT none t x = 0

  q' : ℕ
  q'_pos : 0 < q'

  n : RootIx D → ℤ

  sE : Ωf
  sE_ne : sE ≠ 0

attribute [instance] FixedData.fld FixedData.acg FixedData.mod

structure RootOrigin (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} (Fx : FixedData Y Sys) where

  𝔐 : HodgeCpt Y S RM.y

  Fl : 𝔐.Flag

  g : Fx.Ωf →+* RM.Ω
  g_over : 𝔐.ξ ≫ 𝔐.f = spMap g ≫ Fx.ξf
  g_flag : ∀ s i, (𝔐.M.pt (Fl.b s i)).left ≫ 𝔐.m.φ = spMap (dualMap g) ≫ (Fx.Mf.pt (Fx.bf s i)).left
  g_deg : letI := g.toAlgebra; Module.finrank Fx.Ωf RM.Ω = Fl.deg
  g_const : ∀ a : Fx.Ωf, IsAlgebraic ℤ a → g a ∈ 𝔐.cst.range
  δ_eq : RM.δ = Module.finrank ℚ c.F * Fl.deg

  e : RootIx D → RM.Ω
  lines : Fl.RootLines RM.xdeg e

  sing : RootIx D → HermLine RM.ι
  sing_deg : ∀ r, (sing r).a = RM.xdeg r
  hodge : ∀ r, Fl.IsHodgeLine r (e r) (sing r)

  k₀ : RM.K

  ix : Fin (Fx.m + 1) ≃ RM.ι k₀
  y_eq : ∀ i, RM.y ⟨k₀, ix i⟩ = g (Fx.yf i)
  kA_eq : RM.kA = Fx.kA
  A_deg : RM.A.a k₀ = 1 ∧ ∀ k, k ≠ k₀ → RM.A.a k = 0
  A_h : ∀ z ∈ mcPts RM.P, RM.A.h z = Fx.hf fun i => z ⟨k₀, ix i⟩

  eff : ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (i : Fin (Fx.m + 1)) (t : RM.Ω),
    InChart 𝔐.ξ (fun i' => g (Fx.yf i')) i p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t →
      g Fx.sE * g (Fx.yf i) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧
        (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p (g Fx.sE * g (Fx.yf i) ^ Fx.q' / t))

  Re : PB.Realis Sys RM.P
  Re_deg : Re.deg = Fl.deg
  π_pt : ∀ x, ∃ a : ℂ, (fun i => Re.R.lift x x ⟨k₀, ix i⟩) = a • Fx.pt (Re.π x)
  interior : ∀ x (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ RM.y z (Re.R.lift x x) →
    (𝔐.Interior z ↔ Re.π x ∈ Sys.open')
  fund_deg : ∀ τ i, (Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, RM.xdeg (τ, k)
  fund_sing : ∀ τ i x, Re.π x ∈ Sys.open' →
    Real.log ((Re.ref (some (τ, i))).h (Re.R.lift x x)) + Sys.ph (some (τ, i)) (Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (Re.R.lift x x))
  fund_reg : ∀ τ i t, 0 < t → t ≤ Sys.t₀ → ∀ z ∈ mcPts RM.P,
    Real.log ((Re.line (some (τ, i)) t).h z) = -∑ k ∈ Finset.Iic i, Real.log ((RM.x t (τ, k)).h z)
  ref_none : (Re.ref none).a = RM.A.a ∧ ∀ z ∈ mcPts RM.P, (Re.ref none).h z = RM.A.h z

structure TowerOrigin (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (D.p + D.q)) where
  j_eq : T.j = D.p
  bad_iff : ∀ r : ℕ, r ∈ T.bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M'

  S : ℕ → Finset ℕ
  S_iff : ∀ B r, r ∈ S B ↔ T.InS B r

  Sys : T.Comp → PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))

  Fx : ∀ a, FixedData Y (Sys a)
  comp_inj : ∀ a a', genPt (Fx a).ξf = genPt (Fx a').ξf → a = a'
  comp_onto : ∀ x : Y.X, (∀ x' : Y.X, x' ⤳ x → x' = x) → ∃ a, genPt (Fx a).ξf = x
  nu_eq : ∀ a r, ((Fx a).n r : ℝ) = ((Fx a).kA * (Fx a).q' : ℕ) * T.nu r.1 r.2

  Or : ∀ B a, RootOrigin Y (S B) (T.M B a) (Fx a)

def hostRd (E : Type) [Field E] [NumberField E] : ℝ := |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))

def hostLval (H : Host E) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  let χ : DirichletCharacter ℂ H.d := (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)
  (deriv χ.LFunction 1 / χ.LFunction 1).re

end GlobalTheory.CompanionTheory.Ar
