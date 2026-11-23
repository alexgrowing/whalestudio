import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem conjLinear_onto_of_injective_of_le_range :
    ∀ (W M : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (J₀ J₁ : W →ₗ⋆[ℂ] M), (∀ p ∈ S, ∃ ξ, J₀ ξ = p) → Function.Injective J₁ → (∀ ξ, J₁ ξ ∈ S) → ∀ p ∈ S, ∃ ξ, J₁ ξ = p := by
  intro W M _ _ _ _ _ S J₀ J₁ h0 hinj hS
  let f0 : W →ₗ[ℝ] M :=
    { toFun := J₀
      map_add' := J₀.map_add
      map_smul' := fun r x => by
        show J₀ (r • x) = r • J₀ x
        rw [← Complex.coe_smul, J₀.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }
  let f1 : W →ₗ[ℝ] M :=
    { toFun := J₁
      map_add' := J₁.map_add
      map_smul' := fun r x => by
        show J₁ (r • x) = r • J₁ x
        rw [← Complex.coe_smul, J₁.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }

  have hle0 : S.restrictScalars ℝ ≤ LinearMap.range f0 := fun p hp => h0 p hp
  have hle1 : LinearMap.range f1 ≤ S.restrictScalars ℝ := by
    rintro _ ⟨ξ, rfl⟩
    exact hS ξ
  have hf1 : Function.Injective f1 := hinj
  have : FiniteDimensional ℝ (S.restrictScalars ℝ) := Submodule.finiteDimensional_of_le hle0
  have hdim : Module.finrank ℝ (S.restrictScalars ℝ) ≤ Module.finrank ℝ (LinearMap.range f1) := by
    rw [LinearMap.finrank_range_of_inj hf1]
    exact (Submodule.finrank_mono hle0).trans (LinearMap.finrank_range_le f0)

  have heq : LinearMap.range f1 = S.restrictScalars ℝ := Submodule.eq_of_le_of_finrank_le hle1 hdim
  intro p hp
  have hp' : p ∈ LinearMap.range f1 := heq ▸ hp
  obtain ⟨ξ, hξ⟩ := hp'
  exact ⟨ξ, hξ⟩

end GlobalTheory
