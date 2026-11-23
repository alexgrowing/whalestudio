import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

def WhitenStatement : Prop :=
  ∀ (d : ℕ) (L : Matrix (Fin d) (Fin d) ℝ), L.PosDef →
    ∃ R : Matrix (Fin d) (Fin d) ℝ, IsUnit R.det ∧ L = Rᵀ * R

def HalfTraceStatement : Prop :=
  ∀ (d : ℕ) (L G K R : Matrix (Fin d) (Fin d) ℝ), L = Rᵀ * R → IsUnit R.det → G.PosSemidef →
    Kᵀ * G = -(G * K) → K * L = -(L * Kᵀ) → IsUnit K.det →
    ∀ x : Fin d → ℝ, x ⬝ᵥ (G *ᵥ x) ≤
      (1 / 2) * trace (L * G) * (((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ x))

def ShortDualStatement : Prop :=
  ∀ (d : ℕ) (L R : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ), 0 < d → L = Rᵀ * R → IsUnit R.det → 0 < μ →
    (∀ t : Fin d → ℤ, t ≠ 0 → μ ^ 2 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (L *ᵥ fun i => (t i : ℝ))) →
    ∀ δ : ℝ, 0 < δ → ∃ c : Fin d → Fin d → ℤ, LinearIndependent ℤ c ∧
      ∀ j, ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ≤
        ((d : ℝ) / μ + δ) ^ 2

def FiniteShortStatement : Prop :=
  ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℝ), G.PosDef → ∀ B : ℝ,
    {c : Fin d → ℤ | (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) ≤ B}.Finite

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
