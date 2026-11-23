import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open Module Matrix
open scoped ComplexOrder

def diagForm {ι : Type} [Fintype ι] {m : ι → ℕ}
    (H : (τ : ι) → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (x : (τ : ι) → Fin (m τ) → ℂ) : ℝ :=
  ∑ τ, (star (x τ) ⬝ᵥ (H τ *ᵥ x τ)).re

def ScaleBoundStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (H : (τ : ι) → Matrix (Fin (m τ)) (Fin (m τ)) ℂ),
    (∀ τ, (H τ).PosSemidef) → ∀ (c : ι → ℂ) (C : ℝ), (∀ τ, ‖c τ‖ ^ 2 ≤ C) →
    ∀ x : (τ : ι) → Fin (m τ) → ℂ, diagForm H (fun τ => c τ • x τ) ≤ C * diagForm H x

def ReducedBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Submodule ℤ E) [DiscreteTopology X] [IsZLattice ℝ X] (M : ℝ)
    (v : Fin (finrank ℝ E) → E), LinearIndependent ℝ v → (∀ i, v i ∈ X) →
    (∀ i, ‖v i‖ ^ 2 / 2 ≤ M) →
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ X,
      (∀ j, ‖(b j : E)‖ ^ 2 / 2 ≤ (finrank ℝ E : ℝ) * M) ∧
      ∀ j, ∀ z ∈ X, |inner ℝ (b j : E) z| ≤ 2 * Real.sqrt (finrank ℝ E) * (‖z‖ ^ 2 / 2)

def SpanShortStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (J κ : Type) [Finite J] [Finite κ] (A : J → V →ₗ[ℝ] V) (x : κ → V) (K M : ℝ),
    0 ≤ K → (∀ j y, ‖A j y‖ ^ 2 ≤ K * ‖y‖ ^ 2) → (∀ k, ‖x k‖ ^ 2 / 2 ≤ M) →
    Submodule.span ℝ (Set.range fun p : J × κ => A p.1 (x p.2)) = ⊤ →
    ∃ v : Fin (finrank ℝ V) → J × κ,
      LinearIndependent ℝ (fun i => A (v i).1 (x (v i).2)) ∧
        ∀ i, ‖A (v i).1 (x (v i).2)‖ ^ 2 / 2 ≤ K * M

def PrimeLogSumStatement : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ Real.log x + 2.2

def PrimeTotalStatement : Prop :=
  ∀ (D : ℕ) (L abelian₂ : ℝ) (T : Finset ℕ) (b c : ℕ → ℝ) (g₁ g₂ : ℕ),
    1 ≤ D → Real.log D ≤ 2 * L → 0 ≤ abelian₂ → (∀ l ∈ T, l.Prime) → (∀ l, 0 ≤ c l) →
    ∑ l ∈ T, c l * Real.log l ≤ ((D : ℝ) / 2 + 1) * abelian₂ →
    g₁.Prime → g₂.Prime → 3 ≤ g₁ → 3 ≤ g₂ →
    (∀ l ∈ T, l ≠ g₁ → l ≠ g₂ → l ≤ D → b l ≤ (D : ℝ) / ((l : ℝ) - 1) + c l) →
    (∀ l ∈ T, l ≠ g₁ → l ≠ g₂ → D < l → b l ≤ c l) →
    (∀ l ∈ T, (l = g₁ ∨ l = g₂) → b l ≤ (D : ℝ) / ((l : ℝ) - 1)) →
    ∑ l ∈ T, b l * Real.log l ≤ (2 * L + abelian₂ + 4) * ((D : ℝ) + 2)

def ThirdDiffStatement : Prop :=
  ∀ (G : Type) [AddCommGroup G] (F : G → ℝ), (∃ C : ℝ, ∀ x, |F x| ≤ C) →
    (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) + F x + F y + F z - F 0 = 0) →
    ∀ x, F x = F 0

def NakayamaCharStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (ι : Type) [Fintype ι] (Γ : Type)
    (T : Γ → M →ₗ[R] M) (χ : ι → Γ → R) (s : ι → M),
    Fintype.card ι = finrank R M →
    (∀ i, s i ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) →
    (∀ i γ, T γ (s i) - χ i γ • s i ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) →
    (∀ i j, i ≠ j → ∃ γ, χ i γ - χ j γ ∉ IsLocalRing.maximalIdeal R) →
    Submodule.span R (Set.range s) = ⊤

end ReciprocityTheory.ChartRestriction.G.H1
