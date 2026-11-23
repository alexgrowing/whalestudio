import Mathlib
import Formalism.PeriodIntegrals.BesselL2FixAtZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselSquareIntegrable.SigmaMul

noncomputable section

namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero

open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep PI.BesselL2FixAtZero

def EIntVec : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
  ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w) μG

def SchurHpk : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
  ∃ d : ℝ, 0 < d ∧ ∀ v₁ w₁ v₂ w₂ : H,
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w₁, σ (Matrix.of g) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of g) v₂⟫_ℂ) μG ∧
    ∫ g, ⟪w₁, σ (Matrix.of g) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of g) v₂⟫_ℂ ∂μG =
      ⟪v₂, v₁⟫_ℂ * ⟪w₁, w₂⟫_ℂ / (d : ℂ)

end PI.UnitaryGroupMassFormula.BesselL2FixAtZero
