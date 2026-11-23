import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandD

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_units_subgroup_padic (hK : FiniteDimensional ℚ_[p] K) (E : IntermediateField K (PadicAlgCl p))
    [FiniteDimensional K E] [IsGalois K E] : ∃ S : Subgroup Eˣ,
    (∀ (σ : E ≃ₐ[K] E) (u v : Eˣ), u ∈ S → (v : E) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖((u : E) : PadicAlgCl p)‖ = 1) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : Eˣ, ‖((u : E) : PadicAlgCl p) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : E ≃ₐ[K] E, σ (u : E) = u) → ∃ v ∈ S, ∏ σ : E ≃ₐ[K] E, σ (v : E) = u) ∧
    ∀ σ₀ : E ≃ₐ[K] E, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : E ≃ₐ[K] E, σ (u : E) = 1 →
      ∃ v ∈ S, σ₀ (v : E) = u * v := by
  have hnt : ∃ x : K, 1 < ‖x‖ := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm ℚ_[p]
    refine ⟨algebraMap ℚ_[p] K x, ?_⟩
    show 1 < ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖
    rwa [norm_algebraMap']
  let _ : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := hnt }
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  let _ : NormedAlgebra K E :=
    { (inferInstance : Algebra K E) with
      norm_smul_le := fun a x => le_of_eq (by
        show ‖(a : PadicAlgCl p) * (x : PadicAlgCl p)‖ = _
        rw [norm_mul]; rfl) }
  exact UnitsFilt.exists_units_subgroup (K := K) (L := E)

end ReciprocityTheory.DiscreteGroups.LocalClassField
