import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IntStable

namespace GlobalTheory.CompanionTheory.Ar.HS

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GroundTheory.Heights₂.Heights
open scoped ENNReal

noncomputable section

def HasPS {D : ℕ} (g : (Fin D → ℂ) → ℂ) (Φ : MvPowerSeries (Fin D) ℂ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : Fin D → ℂ),
    ‖g z - ∑ α ∈ multiLe D m,
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm α) Φ * ∏ k, z k ^ α k‖ ≤ C * ‖z‖ ^ (m + 1)

def RatFam {D : ℕ} {K : Type*} [Field K] (g : (K →+* ℂ) → (Fin D → ℂ) → ℂ) : Prop :=
  (∀ τ, AnalyticAt ℂ (g τ) 0) ∧
    ∃ Φ : MvPowerSeries (Fin D) K, ∀ τ, HasPS (g τ) (MvPowerSeries.map τ Φ)

def lin {ι Y : Type*} {m : ℕ} (e : Fin m → ι → Y → ℂ) (c : Fin m → ℂ) : ι → Y → ℂ :=
  fun i y => ∑ k, c k * e k i y

def mon {ι Y : Type*} {D : ℕ} (s : Fin D → ι → Y → ℂ) (α : Fin D → ℕ) : ι → Y → ℂ :=
  fun i y => ∏ k, s k i y ^ α k

def onb {ι Y : Type*} {N : ℕ} (h : HermNorm N) (ω : Fin N → ι → Y → ℂ) : Fin N → ι → Y → ℂ :=
  fun k => lin ω fun j => h.mat⁻¹ j k

section Atlas
variable {D : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas D Y ι La)

def SecEq (F G : ι → Y → ℂ) : Prop := ∀ i y, y ∈ (A.chart i).source → F i y = G i y

def val (F : ι → Y → ℂ) (y : Y) : ℂ := F (A.pick y) y

def ptv {N : ℕ} (ω : Fin N → ι → Y → ℂ) (y : Y) : Fin N → ℂ := fun j => val A (ω j) y

def dS (s : Fin D → ι → Y → ℂ) (i : ι) (y : Y) : ℂ :=
  (fderiv ℂ (fun v : V D => (WithLp.toLp 2 (fun k => s k i ((A.chart i).symm v)) : V D))
    (A.chart i y)).det

def jacF (t : Fin (D + 1) → ι → Y → ℂ) : ι → Y → ℂ := fun i y =>
  (Matrix.of fun a b : Fin (D + 1) => Fin.cases (motive := fun _ => ℂ) (t a i y)
    (fun k => fderiv ℂ (t a i ∘ (A.chart i).symm) (A.chart i y) (bas D k)) b).det

def fsInt {N N₂ : ℕ} (G L L₂ : La) (e : Fin N → ι → Y → ℂ) (e₂ : Fin N₂ → ι → Y → ℂ) (m : ℕ)
    (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (A.nsq G F y / (A.sqn L₂ e₂ y * A.sqn L e y ^ m)) ∂A.mu

def InVnat {N : ℕ} (mu0 L : La) (e : Fin N → ι → Y → ℂ) (j : ℕ) (F : ι → Y → ℂ) : Prop :=
  A.IsSec (mu0 + j • L) F ∧
    ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + j • L) F y * A.sqn L e y ^ (-(j : ℝ))) ∂A.mu < ⊤

def HasJet (w0 : ι → Y → ℂ) (s : Fin D → ι → Y → ℂ) (F G : ι → Y → ℂ) (x : Y)
    (Φ : MvPowerSeries (Fin D) ℂ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
    ‖F (A.pick x) y / G (A.pick x) y - ∑ α ∈ multiLe D m,
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm α) Φ *
        ∏ k, (s k (A.pick x) y / w0 (A.pick x) y) ^ α k‖ ≤
      C * ‖fun k => s k (A.pick x) y / w0 (A.pick x) y‖ ^ (m + 1)

def GoodOver {N : ℕ} (ω : Fin N → ι → Y → ℂ) (J : Set (MvPolynomial (Fin N) ℂ)) (θ : Fin N → ℂ) : Prop :=
  (∀ y, ∀ g ∈ J, MvPolynomial.eval (ptv A ω y) g = 0) ∧
    ∀ (s : Fin D → Fin N → ℂ) (p : Fin N → ℂ), IsTransv J s p → pair θ p ≠ 0 →
      (∃! x, ∃ c : ℂ, ptv A ω x = c • p) ∧
        ∀ x, (∃ c : ℂ, ptv A ω x = c • p) → dS A (fun i => lin ω (s i)) (A.pick x) x ≠ 0

end Atlas

structure Side (D N n₂ : ℕ) (La : Type) [AddCommGroup La] (L L₂ : La) where

  Y : Type
  [top : TopologicalSpace Y]
  [t2 : T2Space Y]
  [sc : SecondCountableTopology Y]
  [ms : MeasurableSpace Y]
  [bs : BorelSpace Y]
  conn : ConnectedSpace Y

  ι : Type

  A : WeightedAtlas D Y ι La

  ω : Fin N → ι → Y → ℂ
  ω_sec : ∀ j, A.IsSec L (ω j)
  ω_gen : ∀ y, ptv A ω y ≠ 0

  b : Fin n₂ → ι → Y → ℂ
  b_sec : ∀ k, A.IsSec L₂ (b k)
  b_gen : ∀ y, ptv A b y ≠ 0

  N₂ : ℕ

  e₂ : Fin N₂ → ι → Y → ℂ
  e₂_sec : ∀ k, A.IsSec L₂ (e₂ k)
  e₂_gen : ∀ y, ptv A e₂ y ≠ 0
  pos : A.Pos (L₂ + D • L) fun _ => 0

attribute [instance] Side.top Side.t2 Side.sc Side.ms Side.bs

def Side.mu0 {D N n₂ : ℕ} {La : Type} [AddCommGroup La] {L L₂ : La} (S : Side D N n₂ La L L₂) : La :=
  S.A.kap + (L₂ + D • L)

end

end GlobalTheory.CompanionTheory.Ar.HS
