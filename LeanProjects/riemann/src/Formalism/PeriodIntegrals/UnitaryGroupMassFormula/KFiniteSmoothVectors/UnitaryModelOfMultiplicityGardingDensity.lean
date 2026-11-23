import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.KFinSmooth
import Formalism.PeriodIntegrals.HCMult

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Defs

variable {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gv (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (x : H) : H :=
  ∫ h, Φ (umat h) • τ (umat h) x ∂(muG ε)

def SmoothJ (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) : Prop :=
  SmoothOnH (Jm ε) (fun g => τ g y)

end Defs

def StepGarding : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ x : H, SmoothJ ε τ (gv ε τ Φ x)

def StepDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ (u : H) (δ : ℝ), 0 < δ →
      ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ ‖gv ε τ Φ u - u‖ < δ

def StepKAvg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ (ν : Measure (UJ ε)), IsFiniteMeasure ν → ν ((KG ε : Set (UJ ε))ᶜ) = 0 →
    ∀ c : UJ ε → ℂ, Continuous c →
    ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∀ x : H,
      ∃ Φ' : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ' ∧ HasCompactSupport Φ' ∧
        ∫ g, c g • τ (umat g) (gv ε τ Φ x) ∂ν = gv ε τ Φ' x

def StepKHaar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ ν : Measure (UJ ε), IsFiniteMeasure ν ∧ ν Set.univ ≠ 0 ∧
    ν ((KG ε : Set (UJ ε))ᶜ) = 0 ∧ ∀ a ∈ KG ε, ν.map (fun g => a * g) = ν

def StepJModel : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ → IsIrredOn (UJset ε) τ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε τ S → ∀ v ∈ S, SmoothJ ε τ v

def StepTopJ : Prop :=
  PI.HCMult → StepGarding → StepDense → StepKAvg → StepKHaar → StepJModel

def StepTransport : Prop := StepJModel → PI.KFinSmooth

def StepConjInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∀ a ∈ KG ε, (muG ε).map (fun g => a * g * a⁻¹) = muG ε

def StepDenseW : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ W : Submodule ℂ H, FiniteDimensional ℂ W →
      ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
        (∀ a ∈ Kset ε, ∀ m, Φ (a * m * aᴴ) = Φ m) ∧
        ∀ w ∈ W, ‖gv ε τ Φ w - w‖ ≤ ‖w‖ / 2

def UnitaryModelOfMultiplicityGardingDensity : Prop :=
  PI.HCMult → StepGarding → StepConjInv → StepDenseW → StepJModel

end PI.KFinSmoothW
