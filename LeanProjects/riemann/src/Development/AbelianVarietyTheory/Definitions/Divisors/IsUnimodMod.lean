import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.Poinc

def qW {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (y : Fin s → X) : ℤ :=
  ∑ u, ∑ v, W u v * β (y u) (y v)

def PosW {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) : Prop := ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef

def CongMod {X : Type} [AddCommGroup X] (N : ℕ) (x y : X) : Prop := ∃ w, x = y + N • w

section Orbit

variable (O : Type) [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X] [Module O X]

def IsUnimodMod (N : ℕ) (k : X₀ →ₗ[ℤ] X) : Prop :=
  (∀ (c : O) x, CongMod N (k (c • x)) (c • k x)) ∧ ∃ ε : X ≃ₗ[ℤ] X₀, (N : ℤ) ∣ LinearMap.det (ε.toLinearMap ∘ₗ k) - 1

def orbit (N₁ N : ℕ) (k : X₀ →ₗ[ℤ] X) {ι : Type} (a : ι → X₀) : Set (ι → X) :=
  {μ | ∃ γ : X₀ →ₗ[ℤ] X₀, (∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) ∧ (N : ℤ) ∣ LinearMap.det γ - 1 ∧
    (∀ x, CongMod N₁ (γ x) x) ∧ ∀ i, CongMod N (μ i) (k (γ (a i)))}

end Orbit

structure FSys {O : Type} [CommRing O] (bar : O → O) (q : ℕ) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N₁ p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [IsLocalRing A] where

  Y : Type

  ev : Y → A →+* PadicAlgCl p
  ev_le : ∀ y h, ‖ev y h‖ ≤ 1
  ev_lt : ∀ y, ∀ h ∈ maximalIdeal A, ‖ev y h‖ < 1

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  β : ∀ y, LinearMap.BilinForm ℤ (X y)
  bal : ∀ y, β y ∈ balForms bar (X y)
  pos : ∀ y x, x ≠ 0 → 0 < β y x x

  sc : Y → ℝ
  sc_pos : ∀ y, 0 < sc y

  Q : Type

  t : ∀ y, (Fin s → X y) → Q → PadicAlgCl p
  t_le : ∀ y μ c, ‖t y μ c‖ ≤ Real.exp (-(sc y * qW W (β y) μ))
  t_eq : ∀ y μ, ∃ c, ‖t y μ c‖ = Real.exp (-(sc y * qW W (β y) μ))
  lam : ∃ C : ℝ, ∀ y x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Real.exp (-(C * (sc y * β y x x))) ≤ ‖ev y h‖
  four : ∀ (y₀ : Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, X y₀ →ₗ[ℤ] X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∀ (m : ℕ) (a : Fin m × Fin s → X y₀) (c : Fin m → Q) (e : ℕ), ∃ f : A, ∀ y,
      ∃ h ∈ maximalIdeal A, ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Fin m × Fin s → X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
        (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → Real.exp (-(sc y * ∑ i, (qW W (β y) (fun u => μ (i, u)) : ℝ))) < ε) ∧
        ‖ev y f - ∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i)‖ ≤ max ε (‖ev y h‖ ^ e)

attribute [instance] FSys.add FSys.mod FSys.fin FSys.proj FSys.freeZ FSys.finZ

def FSys.Approx {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ p : ℕ} [Fact p.Prime]
    {A : Type} [CommRing A] [IsLocalRing A] (Φ : FSys bar q W N₁ p A) (φ : InvFun O) (d : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (e : ℕ), ∃ f : A, ‖Φ.ev y₀ f‖ = Real.exp (-(Φ.sc y₀ * (d * φ.evalZ (Φ.β y₀)))) ∧
    ∀ y, ‖Φ.ev y f‖ ≤ Real.exp (-(Φ.sc y * (d * φ.evalZ (Φ.β y)))) ∨ ∃ h ∈ maximalIdeal A, ‖Φ.ev y f‖ ≤ ‖Φ.ev y h‖ ^ e

structure Supports {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (d : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {r : ℕ} (γ : Fin r → LinearMap.BilinForm ℤ X) {m : ℕ} (a : Fin m → X) : Prop where
  span : Submodule.span ℤ (Set.range a) = ⊤
  le : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → d * φ.evalZ β ≤ (∑ i, β (a i) (a i) : ℤ)
  eq : ∀ j, d * φ.evalZ (γ j) = (∑ i, γ j (a i) (a i) : ℤ)
  only : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → d * φ.evalZ β = (∑ i, β (a i) (a i) : ℤ) →
    ∃ (k : ℕ) (c : Fin r → ℕ), 0 < k ∧ k • β = ∑ j, c j • γ j

def HasSupports {O : Type} [CommRing O] (bar : O → O) (q : ℕ) (φ : InvFun O) (d : ℕ) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → X), Supports bar φ d γ a

def BddAct {O : Type} [CommRing O] (bar : O → O) : Prop :=
  ∀ c : O, ∃ C : ℤ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
    ∀ x, β (c • x) (c • x) ≤ C * β x x

end GlobalTheory.Poinc
