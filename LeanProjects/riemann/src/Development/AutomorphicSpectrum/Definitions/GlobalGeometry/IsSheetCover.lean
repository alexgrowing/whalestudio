import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {n : ℕ}

def torusSat (T : Set ((Σ k, J k) → ℂ)) : Set ((Σ k, J k) → ℂ) :=
  {w | ∃ w' ∈ T, ∃ a : K → ℂ, (∀ k, a k ≠ 0) ∧ w = torusSmul a w'}

structure IsSheetCover {P : Ideal (MRing J)} {Bd : Set ((Σ k, J k) → ℂ)} {nc : ℕ} (χ : Fin nc → SncChart P n Bd)
    (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) : Prop where
  isOpen : ∀ m, IsOpen (V m)
  hol : ∀ m, DifferentiableOn ℂ (γ m) (V m)
  mem : ∀ m, ∀ t ∈ V m, γ m t ∈ mcPts P \ Bd
  inj : ∀ m, ∀ t ∈ V m, ∀ t' ∈ V m, γ m t ∈ torusSat {γ m t'} → t = t'
  meas : ∀ m, MeasurableSet (B m) ∧ B m ⊆ V m
  disj : ∀ m m', m ≠ m' → ∀ t ∈ B m, γ m t ∉ torusSat (γ m' '' B m')
  cover : ∀ a, volume {t ∈ Metric.ball (0 : Fin n → ℂ) 1 | (χ a).γ t ∉ torusSat (⋃ m, γ m '' B m)} = 0

end Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}

structure Pieces (Or : CptOrigin Y S₀ Dc Hd) where

  np : ℕ

  g : ℕ

  Λ : Fin np → Type
  [acg : ∀ k, AddCommGroup (Λ k)]
  [mod : ∀ k, Module (𝓞 E) (Λ k)]

  F : ∀ k, UnivFam E (CMType H) Dc.j Dc.j' Dc.n g (Λ k)

  Γ : ∀ k, Subgroup (Λ k ≃ₗ[𝓞 E] Λ k)
  arith : ∀ k, (F k).IsArith (Γ k)

  FF : Fin np → Set (Fin Dc.n → ℂ)
  fund : ∀ k, (F k).IsFundSet (Γ k) (FF k)

  d : Fin np → ℕ
  d_pos : ∃ k, 0 < d k

  pc : ℕ → Fin np

  V : ℕ → Set (Fin Dc.n → ℂ)

  B : ℕ → Set (Fin Dc.n → ℂ)

  γ : ℕ → (Fin Dc.n → ℂ) → (Σ k, J k) → ℂ
  cover : IsSheetCover Dc.chart V B γ
  V_sub : ∀ m, V m ⊆ ballDom (F (pc m)).q
  B_sub : ∀ m, B m ⊆ FF (pc m)
  count : ∀ k, ∀ᵐ t, t ∈ FF k → {m | pc m = k ∧ t ∈ B m}.encard = d k
  fibre : ∀ m, ∀ t ∈ V m, ∃ z : Sp ℂ ⟶ Or.𝔐.X, CoordsAt Or.𝔐.ξ Dc.y z (γ m t) ∧ Or.𝔐.Interior z ∧
    FibreLat Or.𝔐.t z ((F (pc m)).R t) ∧ Or.𝔐.LabVal z Or.sm (F (pc m)).σ
  pot : ∀ m, ∀ t ∈ V m, ∃ G : (Fin Dc.n → ℂ) → ℂ, AnalyticAt ℂ G t ∧
    ∀ᶠ t' in 𝓝 t, phMu Hd (γ m t') = ballPot (F (pc m)).q t' / 2 + (G t').re

attribute [instance] Pieces.acg Pieces.mod

end GlobalTheory.CompanionTheory.Ar.Cusp
