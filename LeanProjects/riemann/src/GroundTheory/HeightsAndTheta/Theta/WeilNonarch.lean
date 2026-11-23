import Mathlib
import GroundTheory.HeightsAndTheta.Theta.WeilBox

noncomputable section

namespace GroundTheory.Heights₂.Theta

open GroundTheory.LocalField ValuativeRel MeasureTheory Measure Topology Filter Matrix
open scoped WithZero NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def quadForm (A : Matrix ι ι F) (x : ι → F) : F := x ⬝ᵥ A *ᵥ x

variable [MeasurableSpace F] [BorelSpace F]

def gaussBox (ψ : AddChar F Circle) (A : Matrix ι ι F) (N : ℤ) : ℂ :=
  ∫ x in (valBox F ι (-N) : Set (ι → F)), (ψ (quadForm A x) : ℂ) ∂selfDualPi ι ψ

def IsWeilIndex (ψ : AddChar F Circle) (A : Matrix ι ι F) (γ : ℂ) : Prop :=
  ∀ f ∈ schwartzBruhatPi F ι,
    ∫ x, fourierPi ψ f x * (ψ (quadForm A x) : ℂ) ∂selfDualPi ι ψ =
      γ * (((NNReal.sqrt (modulus ((2 : F) • A).det))⁻¹ : ℝ≥0) : ℝ) *
        ∫ y, f y * (ψ (-(quadForm A⁻¹ y) / 4) : ℂ) ∂selfDualPi ι ψ

open Classical in

def weilIndex (ψ : AddChar F Circle) (A : Matrix ι ι F) : ℂ :=
  if h : ∃ γ, IsWeilIndex ψ A γ then h.choose else 0

variable {ψ : AddChar F Circle}

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ

include hψ1

end GroundTheory.Heights₂.Theta
