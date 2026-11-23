import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

def punct (n a : ℕ) (ρ : ℝ) : Set (Fin n → ℂ) := {z | z ∈ Metric.ball 0 ρ ∧ ∀ i : Fin n, i.val < a → z i ≠ 0}

def logSize {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : ℝ :=
  1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

structure BdryChart (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) where
  a_le : a ≤ n

  R : Type
  [ring : CommRing R]

  t : SAB H (Sp R)

  g : ℕ
  dim : SmoothOfRelativeDimension g t.G.hom

  M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)

  ψ : (Fin n → ℂ) → (R →+* ℂ)
  hol : IsHolPts (Metric.ball 0 1) ψ

  V : Scheme.{0}

  j : V ⟶ Sp R
  j_open : IsOpenImmersion j

  k : V ⟶ Xo.X

  tV : SAB H V

  m₁ : SABMap tV t j

  m₂ : SABMap tV Xo.univ.t k

  pt : (Fin n → ℂ) → (Sp ℂ ⟶ V)
  pt_eq : ∀ z ∈ punct n a 1, pt z ≫ j = spMap (ψ z) ∧ pt z ≫ k ≫ Xo.s = spMap σ

attribute [instance] BdryChart.ring

def BdryChart.IsVal {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ) {m : ℕ}
    (u : Fin m → Fin C.g → C.R) (v : Fin m → (epsAt (spMap (C.ψ z)) ⟶ C.t.G)) : Prop :=
  ∀ i, (v i).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u i)).left

def BdryChart.IsRiem {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ)
    (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) : Prop :=
  ∀ (m : ℕ) (u : Fin m → Fin C.g → C.R) (v : Fin m → (epsAt (spMap (C.ψ z)) ⟶ C.t.G))
    (Γ : Matrix (Fin m) (Fin m) ℂ), C.IsVal z u v →
    (IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ ↔
      ∀ i j, Γ i j = Real.pi * hermForm Hm (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b)))

end GlobalTheory.CompanionTheory.Ar.Flat
