import Mathlib
import GroundTheory.LocalFields.LocalFourier
import GroundTheory.AutomorphicForms.MeasuresModulus

noncomputable section

namespace GroundTheory.Heights₂.Theta

open GroundTheory.LocalField ValuativeRel MeasureTheory Measure Topology Filter Matrix
open scoped WithZero NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {ι : Type*} [Fintype ι]

section Boxes

variable (F ι) in

def valBox (n : ℤ) : AddSubgroup (ι → F) := AddSubgroup.pi Set.univ fun _ => valBall F n

variable [MeasurableSpace F] [BorelSpace F]

end Boxes

section SchwartzBruhat

variable (F ι) in

def schwartzBruhatPi : Submodule ℂ ((ι → F) → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ => c)⟩

end SchwartzBruhat

section Fourier

variable [MeasurableSpace F] [BorelSpace F]

variable (ι) in

def selfDualPi (ψ : AddChar F Circle) : Measure (ι → F) :=
  Measure.pi fun _ : ι => selfDualMeasure ψ

instance (ψ : AddChar F Circle) : (selfDualPi ι ψ).IsAddHaarMeasure := by
  unfold selfDualPi
  infer_instance

def fourierPi (ψ : AddChar F Circle) (f : (ι → F) → ℂ) (y : ι → F) : ℂ :=
  ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂selfDualPi ι ψ

variable {ψ : AddChar F Circle}

theorem continuous_dotProduct_right (y : ι → F) : Continuous fun x : ι → F => x ⬝ᵥ y :=
  continuous_id.dotProduct continuous_const

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ

theorem continuous_char_comp {g : (ι → F) → F} (hg : Continuous g) :
    Continuous fun x => (ψ (g x) : ℂ) :=
  (continuous_subtype_val.comp hψ).comp hg

theorem integrable_mul_char_of_mem_schwartzBruhatPi {f : (ι → F) → ℂ}
    (hf : f ∈ schwartzBruhatPi F ι) (y : ι → F) :
    Integrable (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) (selfDualPi ι ψ) :=
  (hf.1.continuous.mul (continuous_char_comp hψ (continuous_dotProduct_right y))).integrable_of_hasCompactSupport
    hf.2.mul_right

include hψ1

end Fourier

end GroundTheory.Heights₂.Theta
