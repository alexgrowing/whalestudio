import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.Poinc

structure FPre {O : Type} [CommRing O] (bar : O → O) (q p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsLocalRing A] where

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

attribute [instance] FPre.add FPre.mod FPre.fin FPre.proj FPre.freeZ FPre.finZ

namespace FPre

variable {O : Type} [CommRing O] {bar : O → O} {q p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : FPre bar q p A) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)

def abelian₂ : Prop :=
  ∃ C : ℝ, ∀ y x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Real.exp (-(C * (Φ.sc y * Φ.β y x x))) ≤ ‖Φ.ev y h‖

def IsTerms {Q : Type} (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  (∀ y μ c, ‖t y μ c‖ ≤ Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))) ∧
    ∀ y μ, ∃ c, ‖t y μ c‖ = Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))

def OrbitSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  ∀ (m : ℕ) (a : Fin m × Fin s → Φ.X y₀) (c : Fin m → Q) (e : ℕ), ∃ f : A, ∀ y,
    ∃ h ∈ maximalIdeal A, ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Fin m × Fin s → Φ.X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
      (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → Real.exp (-(Φ.sc y * ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ))) < ε) ∧
      ‖Φ.ev y f - ∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i)‖ ≤ max ε (‖Φ.ev y h‖ ^ e)

def Four (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type)
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod O N (k y)) ∧ Φ.IsTerms W t ∧
      Φ.OrbitSums W N₁ N y₀ k t

def Approx (φ : InvFun O) (d : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (e : ℕ), ∃ f : A, ‖Φ.ev y₀ f‖ = Real.exp (-(Φ.sc y₀ * (d * φ.evalZ (Φ.β y₀)))) ∧
    ∀ y, ‖Φ.ev y f‖ ≤ Real.exp (-(Φ.sc y * (d * φ.evalZ (Φ.β y)))) ∨ ∃ h ∈ maximalIdeal A, ‖Φ.ev y f‖ ≤ ‖Φ.ev y h‖ ^ e

def ClassSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) (B : Type) [CommRing B] [Algebra A B] (𝔷 : Ideal B) : Prop :=
  ∃ (ev' : Φ.Y → B →+* PadicAlgCl p) (f : (Fin s → Φ.X y₀) → Q → B),
    (∀ y a, ev' y (algebraMap A B a) = Φ.ev y a) ∧ (∀ y b, ‖ev' y b‖ ≤ 1) ∧ (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) ∧
    (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧
    (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin s → Φ.X y), ∀ S : Finset (Fin s → Φ.X y),
      (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) →
        ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧
    ∀ σ : B ≃ₐ[A] B, 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) ∧
      (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod N₁ (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ

end FPre

end GlobalTheory.Poinc
