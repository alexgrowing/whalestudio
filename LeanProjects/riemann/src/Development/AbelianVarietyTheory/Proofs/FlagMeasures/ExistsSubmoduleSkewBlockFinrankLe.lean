import Mathlib

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

def skewOpsBlock (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Submodule ℝ (F →L[ℂ] F) where
  carrier := {M | ∀ x z, ⟪M x, z⟫_ℂ + ⟪x, M z⟫_ℂ = 0}
  zero_mem' := by intro x z; simp
  add_mem' := by
    intro a b ha hb x z
    have h1 := ha x z
    have h2 := hb x z
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    linear_combination h1 + h2
  smul_mem' := by
    intro c a ha x z
    have h1 := ha x z
    have e : ∀ y, (c • a) y = (c : ℂ) • a y := fun y => by
      simp [Complex.coe_smul]
    simp only [e, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (c : ℂ) * h1

theorem finrank_skewOpsBlock_le (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    Module.finrank ℝ (skewOpsBlock F) ≤ Module.finrank ℂ F ^ 2 := by
  let J : (F →L[ℂ] F) →ₗ[ℝ] (F →L[ℂ] F) :=
    { toFun := fun M => Complex.I • M
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun c a => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  have hJ : Function.Injective J := by
    intro a b h
    exact smul_right_injective _ Complex.I_ne_zero h
  have hd : Disjoint (skewOpsBlock F) ((skewOpsBlock F).map J) := by
    rw [Submodule.disjoint_def]
    rintro a ha ⟨b, hb, rfl⟩
    have hb0 : b = 0 := by
      ext x
      have h1 := ha x (b x)
      have h2 := hb x (b x)
      have e : ∀ y, J b y = Complex.I • b y := fun y => rfl
      simp only [e, inner_smul_left, inner_smul_right, Complex.conj_I] at h1
      have h3 : ⟪b x, b x⟫_ℂ = 0 := by
        linear_combination (Complex.I / 2) * h1 + (1 / 2 : ℂ) * h2 +
          ((⟪b x, b x⟫_ℂ - ⟪x, b (b x)⟫_ℂ) / 2) * Complex.I_mul_I
      simpa using h3
    rw [hb0, map_zero]
  haveI : FiniteDimensional ℝ (F →L[ℂ] F) := FiniteDimensional.complexToReal _
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [← (Submodule.equivMapOfInjective J hJ (skewOpsBlock F)).finrank_eq,
    finrank_real_of_complex] at h1
  have h2 : Module.finrank ℂ (F →L[ℂ] F) = Module.finrank ℂ F ^ 2 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := F) (F' := F)).finrank_eq,
      Module.finrank_linearMap, sq]
  omega

theorem exists_submodule_skew_block_finrank_le (n : ℕ)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ Module.finrank ℂ E ^ 2 ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        (∀ x ∈ E, ∀ z ∈ E, ⟪T x, z⟫_ℂ + ⟪x, T z⟫_ℂ = 0) →
          E.starProjection ∘L T ∘L E.starProjection ∈ U := by
  let Φ : (E →L[ℂ] E) →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun a b => by ext1 x; rfl
      map_smul' := fun c a => by ext1 x; rfl }
  haveI : FiniteDimensional ℝ (E →L[ℂ] E) := FiniteDimensional.complexToReal _
  refine ⟨(skewOpsBlock E).map Φ,
    (Submodule.finrank_map_le Φ _).trans (finrank_skewOpsBlock_le E), ?_⟩
  intro T hT
  refine ⟨E.orthogonalProjection ∘L T ∘L E.subtypeL, ?_, ?_⟩
  · intro x z
    have := hT x x.2 z z.2
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.inner_orthogonalProjection_eq_of_mem_left,
      Submodule.inner_orthogonalProjection_eq_of_mem_right]
    exact this
  · ext1 x; rfl

end GlobalTheory
