import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

noncomputable section

universe u

def polyAt (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n) : ℂ :=
  MvPolynomial.eval (fun i => w i) Δ

def VanishOrder {M : Type u} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (x : M)
    (N : ℕ) : Prop :=
  f =O[𝓝 x] fun y => ‖z y - z x‖ ^ N

open Classical in

def fiberVals {M : Type u} (n : ℕ) (z : M → V n) (u : M → ℂ) (w : V n) : Multiset ℂ :=
  if h : (z ⁻¹' {w}).Finite then h.toFinset.val.map u else 0

def fiberSymm {M : Type u} (n : ℕ) (z : M → V n) (u : M → ℂ) (k : ℕ) (w : V n) : ℂ :=
  (fiberVals n z u w).esymm k

def lineVanishStatement : Prop :=
  ∀ (g : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (K N : ℕ), B.Finite → K < N →
    DifferentiableOn ℂ g Bᶜ → (∀ t ∉ B, ‖g t‖ ≤ A * (1 + ‖t‖) ^ K) →
    (g =O[𝓝 0] fun t => t ^ N) → ∀ t ∉ B, g t = 0

def esymmZeroStatement : Prop :=
  ∀ s : Multiset ℂ, (∀ k : ℕ, 1 ≤ k → s.esymm k = 0) → ∀ a ∈ s, a = 0

def sheetsStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)) (u : M → ℂ),
    IsCoveringMapOn z U → ∀ w ∈ U, (z ⁻¹' {w}).Finite →
    ∃ (W : Set (V n)) (d : ℕ) (s : Fin d → V n → M), IsOpen W ∧ w ∈ W ∧
      (∀ i, ContinuousOn (s i) W) ∧ (∀ i, ∀ v ∈ W, z (s i v) = v) ∧
      ∀ v ∈ W, fiberVals n z u v = (Finset.univ : Finset (Fin d)).val.map (fun i => u (s i v))

def symmDiffStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)) (u : M → ℂ),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ w ∈ U, (z ⁻¹' {w}).Finite) →
    Holo n z u → ∀ (k : ℕ), ∀ w ∈ U, DifferentiableAt ℂ (fiberSymm n z u k) w

def symmVanishStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)) (u : M → ℂ)
    (w₀ : V n) (N : ℕ),
    IsCoveringMapOn z U → w₀ ∈ U → (z ⁻¹' {w₀}).Finite →
    (∀ x, z x = w₀ → VanishOrder n z u x N) →
    ∀ k : ℕ, fiberSymm n z u k =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (k * N)

def symmGrowthStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) (z : M → V n) (u : M → ℂ) (R : V n → ℝ) (δ : ℕ),
    (∀ x, ‖u x‖ ≤ R (z x)) → (∀ w, (z ⁻¹' {w}).encard ≤ δ) →
    ∀ (k : ℕ) (w : V n), ‖fiberSymm n z u k w‖ ≤ 2 ^ δ * (max (R w) 0) ^ k

def lineFiniteStatement : Prop :=
  ∀ (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n), polyAt n Δ 0 ≠ 0 →
    {t : ℂ | polyAt n Δ (t • w) = 0}.Finite

def holoSectionStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (f : M → ℂ),
    IsLocalHomeomorph z → Holo n z f → ∀ (s : V n → M) (w : V n),
      ContinuousAt s w → (∀ᶠ v in 𝓝 w, z (s v) = v) → DifferentiableAt ℂ (f ∘ s) w

def normVanishStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (Δ : MvPolynomial (Fin n) ℂ)
    (δ m : ℕ) (C : ℝ) (u : M → ℂ),
    polyAt n Δ 0 ≠ 0 →
    IsCoveringMapOn z {w | polyAt n Δ w ≠ 0} →
    (∀ x, polyAt n Δ (z x) ≠ 0) →
    (∀ w, (z ⁻¹' {w}).encard ≤ δ) →
    Holo n z u →
    (∀ x, ‖u x‖ ≤ C * (1 + ‖z x‖ ^ 2) ^ ((m : ℝ) / 2)) →
    (∀ x, z x = 0 → VanishOrder n z u x (m + 1)) →
    ∀ x, u x = 0

end

end ReciprocityTheory.L2DbarEstimates.Norm
