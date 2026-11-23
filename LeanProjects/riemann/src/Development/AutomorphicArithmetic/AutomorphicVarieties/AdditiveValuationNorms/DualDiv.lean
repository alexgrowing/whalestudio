import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Formalism.GaloisCohomology.Statement
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj

open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.dualDiv :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (x : D →ₗ[ℤ_[l]] QZ l), (∀ φ : D, (l : ℤ_[l]) • φ = 0 → x φ = 0) →
      ∃ y : D →ₗ[ℤ_[l]] QZ l, x = (l : ℤ_[l]) • y := by
  intro l _ D _ _ x hx
  let μ : D →ₗ[ℤ_[l]] D := (l : ℤ_[l]) • LinearMap.id
  have hker : LinearMap.ker μ ≤ LinearMap.ker x := by
    intro φ hφ
    exact hx φ (by simpa [μ] using hφ)
  let g : LinearMap.range μ →ₗ[ℤ_[l]] QZ l :=
    ((LinearMap.ker μ).liftQ x hker).comp (LinearMap.quotKerEquivRange μ).symm.toLinearMap
  obtain ⟨y, hy⟩ := (qzInj l).out (LinearMap.range μ).subtype Subtype.val_injective g
  refine ⟨y, ?_⟩
  ext φ
  have hmem : μ φ ∈ LinearMap.range μ := LinearMap.mem_range_self μ φ
  have h1 := hy ⟨μ φ, hmem⟩
  have h3 : (LinearMap.quotKerEquivRange μ).symm ⟨μ φ, hmem⟩ = Submodule.Quotient.mk φ := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have h2 : g ⟨μ φ, hmem⟩ = x φ := by
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [h3, Submodule.liftQ_apply]
  rw [h2] at h1
  simp only [Submodule.coe_subtype, μ, LinearMap.smul_apply, LinearMap.id_apply] at h1
  rw [LinearMap.smul_apply, ← h1, map_smul]
