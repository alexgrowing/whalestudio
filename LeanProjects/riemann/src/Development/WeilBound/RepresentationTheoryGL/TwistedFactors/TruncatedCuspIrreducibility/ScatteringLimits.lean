import Mathlib
import GroundTheory.AutomorphicForms.TraceClass

noncomputable section

open MeasureTheory GroundTheory.Automorphic
open scoped InnerProductSpace

namespace PositivityTheory.Rg.Tf.IntegralApplyAeEq

abbrev L (V : Type) [NormedAddCommGroup V] : Type := Lp V 2 (volume : Measure ℝ)

variable {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

def Ker (κ : ℝ → V →L[ℂ] W) : Prop := Continuous κ ∧ HasCompactSupport κ

def symb (κ : ℝ → V →L[ℂ] W) (z : ℂ) : V →L[ℂ] W := ∫ t : ℝ, Complex.exp (z * t) • κ t

def Conv (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) : Prop :=
  ∀ (u : L V) (v : L W), (∀ᵐ x : ℝ, v x = ∫ t : ℝ, κ t (u (x + t))) → X (J u) = J' v

def IsTrunc (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (T : ℝ) (Λ : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint Λ ∧ Λ ∘L Λ = Λ ∧ ∀ h : H, Λ h = 0 ↔
    ∃ (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ T → u x = 0) ∧ (∀ᵐ x : ℝ, x ≤ T → v x = 0) ∧ h = J u + J' v

structure Datum (H V W : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] where
  J : L V →ₗᵢ[ℂ] H
  J' : L W →ₗᵢ[ℂ] H
  T₀ : ℝ
  B : H →L[ℂ] H
  β : ℝ → V →L[ℂ] V
  β' : ℝ → W →L[ℂ] W
  span : ∀ h : H, (∀ u, ⟪J u, h⟫_ℂ = 0) → (∀ v, ⟪J' v, h⟫_ℂ = 0) → h = 0
  shift : ∀ (t : ℝ) (u u' : L V) (v v' : L W), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
    ⟪J u', J' v⟫_ℂ = ⟪J u, J' v'⟫_ℂ
  causal : ∀ (s : ℝ) (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * T₀ - s → v x = 0) →
    ⟪J u, J' v⟫_ℂ = 0
  β_ker : Ker β
  β'_ker : Ker β'
  β_unit : IsUnit (symb β 0)
  β'_unit : IsUnit (symb β' 0)
  B_sa : IsSelfAdjoint B
  B_J : Conv J J B β
  B_J' : Conv J' J' B β'
  compact : ∀ (T : ℝ) (Λ : H →L[ℂ] H), T₀ ≤ T → IsTrunc J J' T Λ → IsCompactOperator (Λ ∘L B ∘L Λ)

def Main : Prop :=
  ∀ (H V W : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (D : Datum H V W),
    ∃ N : W ≃ₗᵢ[ℂ] V,
      (∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → Conv D.J D.J Y β → Conv D.J' D.J' Y β' →
        ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
      ∀ (X Λ : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) (T K : ℝ), Ker κ → Conv D.J D.J' X κ → D.T₀ ≤ T → IsTrunc D.J D.J' T Λ →
        IsTraceClass (Λ ∘L X ∘L Λ) →
        (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ K / (1 + |z.im|)) →
        ‖trace (Λ ∘L X ∘L Λ) -
            (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
          Module.finrank ℂ V * Real.exp (2 * D.T₀) * K * Real.exp (-2 * T)

end PositivityTheory.Rg.Tf.IntegralApplyAeEq
