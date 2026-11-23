import Mathlib
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_one_add_comp_comm_field {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
    (A : V →ₗ[K] W) (B : W →ₗ[K] V) :
    LinearMap.det (1 + A ∘ₗ B) = LinearMap.det (1 + B ∘ₗ A) := by
  classical
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  rw [← LinearMap.det_toMatrix bW, ← LinearMap.det_toMatrix bV, map_add, map_add,
    LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_comp bV bW bV,
    LinearMap.toMatrix_one, LinearMap.toMatrix_one, Matrix.det_one_add_mul_comm]

theorem exists_det_congr_one : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] (I : Ideal (𝓞 E)) (g : La →ₗ[𝓞 E] La), (∀ a, g a - a ∈ I • (⊤ : Submodule (𝓞 E) La)) → ∃ u : 𝓞 E, u - 1 ∈ I ∧ (u : E) = LinearMap.det (g.baseChange E) := by
  intro E _ _ La _ _ _ _ I g hg
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) La
  set N : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → 𝓞 E) := i ∘ₗ ((g - 1) ∘ₗ p) with hN
  have key : ∀ (x : La), x ∈ I • (⊤ : Submodule (𝓞 E) La) → ∀ k, i x k ∈ I := by
    intro x hx k
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x y hx hy
      rw [map_add, Pi.add_apply]
      exact I.add_mem hx hy
  refine ⟨LinearMap.det (1 + N), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, ← LinearMap.det_toMatrix', RingHom.map_det, map_one]
    have : (Ideal.Quotient.mk I).mapMatrix (LinearMap.toMatrix' (1 + N)) = 1 := by
      rw [map_add, map_add, LinearMap.toMatrix'_one, map_one, add_eq_left]
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
        LinearMap.toMatrix'_apply]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact key _ (hg _) _
    rw [this, Matrix.det_one]
  · have h1 : ((LinearMap.det (1 + N) : 𝓞 E) : E) = LinearMap.det ((1 + N).baseChange E) :=
      (LinearMap.det_baseChange (A := E) (1 + N)).symm
    rw [h1, LinearMap.baseChange_add, LinearMap.baseChange_one, hN, LinearMap.baseChange_comp,
      det_one_add_comp_comm_field, ← LinearMap.baseChange_comp, LinearMap.comp_assoc, hpi,
      LinearMap.comp_id, LinearMap.baseChange_sub, LinearMap.baseChange_one, add_sub_cancel]

end GlobalTheory.CompanionTheory.Ar.Flat
