import Mathlib
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.UnitsBasic

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

instance integerUnitsAction : MulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ where
  smul σ u := Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u
  one_smul u := by ext; rfl
  mul_smul σ τ u := by ext; rfl
  smul_mul σ u w := map_mul (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])) u w
  smul_one σ := map_one (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]))

@[simp]
theorem coe_smul_integerUnits (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    (((σ • u : 𝒪[L]ˣ) : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L) :=
  rfl

theorem unitsIncl_smul (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    unitsIncl L (σ • u) = σ • unitsIncl L u := by
  ext
  rfl

end GroundTheory.LocalField
