import Mathlib

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhSchurConv

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ

def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)

def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ

def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def SchurConv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (Hσ : Type) [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
    (σ : G → (Hσ →L[ℂ] Hσ)) (d : ℝ) (w : Hσ),
    IsURep σ → IsFdegG μ σ d → ‖w‖ = 1 →
      PhConv μ (phOf σ w d) (coefM σ w) ∧
      ∀ u u' : Hσ, Integrable (fun g => phOf σ w d g * ⟪u', σ g u⟫_ℂ) μ ∧
        ∫ g, phOf σ w d g * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ

end PI.PhSchurConv
