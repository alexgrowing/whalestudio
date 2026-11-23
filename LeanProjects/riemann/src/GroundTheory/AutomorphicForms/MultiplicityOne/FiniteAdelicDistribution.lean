import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicGroups

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Filter Set

open scoped RestrictedProduct

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

def pullL {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    locallyConstantCompactSupport Y ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport X ℂ ℂ where
  toFun φ := ⟨(φ : Y → ℂ) ∘ e, mem_locallyConstantCompactSupport.2
    ⟨φ.2.1.comp_continuous e.continuous, φ.2.2.comp_homeomorph e⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_pullL {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (φ : locallyConstantCompactSupport Y ℂ ℂ) :
    ((pullL e φ : locallyConstantCompactSupport X ℂ ℂ) : X → ℂ) = (φ : Y → ℂ) ∘ e := rfl

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

end

end Whittaker

end GroundTheory.Automorphic
