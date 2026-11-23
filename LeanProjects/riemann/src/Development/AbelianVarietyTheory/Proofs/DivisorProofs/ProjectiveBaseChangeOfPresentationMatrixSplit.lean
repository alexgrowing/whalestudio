import Mathlib
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_of_presentation_split
    (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (r : Fin m → Fin n → R) (hr : Submodule.span R (Set.range r) = LinearMap.ker π)
    (v : Fin n → Fin n → B) (w : Fin n → Fin m → B)
    (hv : ∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0)
    (hvw : ∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) :
    Module.Projective B (B ⊗[R] M) := by
  classical

  let φ : (Fin n → R) →ₗ[R] (Fin n → B) := ∑ a, (LinearMap.proj a).smulRight (v a)
  have hφ : ∀ x l, φ x l = ∑ a, algebraMap R B (x a) * v a l := by
    intro x l
    simp [φ, Finset.sum_apply, Algebra.smul_def]
  have hker : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hr, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    funext l
    rw [hφ]
    simpa using hv b l
  let ψ : M →ₗ[R] (Fin n → B) :=
    (LinearMap.ker π).liftQ φ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hψ : ∀ x, ψ (π x) = φ x := by
    intro x
    have : (π.quotKerEquivOfSurjective hπ).symm (π x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp [ψ, this]
  let i : B ⊗[R] M →ₗ[B] (Fin n → B) := ψ.liftBaseChange B
  let s : (Fin n → B) →ₗ[B] B ⊗[R] M :=
    ∑ l, (LinearMap.proj l).smulRight ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
  have hs : ∀ y, s y = ∑ l, y l • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) := by
    intro y; simp [s]
  have hsr : ∀ b, ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
    intro b
    have h0 : π (r b) = 0 := by
      rw [← LinearMap.mem_ker, ← hr]; exact Submodule.subset_span ⟨b, rfl⟩
    have : ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
        = (1 : B) ⊗ₜ[R] π (r b) := by
      conv_rhs => rw [show r b = ∑ l, r b l • Pi.single l (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, tmul_sum, algebraMap_smul, tmul_smul]
    rw [this, h0, tmul_zero]
  have hsv : ∀ a, s (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := by
    intro a
    rw [hs]
    simp_rw [hvw a, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ l, (w a b * algebraMap R B (r b l)) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
      intro b
      simp_rw [mul_smul, ← Finset.smul_sum, hsr, smul_zero]
    simp [this, ite_smul]
  have hsi : s ∘ₗ i = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    obtain ⟨z, rfl⟩ := hπ y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, i, LinearMap.liftBaseChange_tmul, map_smul]
    have hz : φ z = ∑ a, z a • v a := by
      funext l; rw [hφ]; simp [Finset.sum_apply, Algebra.smul_def]
    rw [hψ, hz, map_sum]
    simp_rw [LinearMap.map_smul_of_tower, hsv]
    conv_rhs => rw [show z = ∑ a, z a • Pi.single a (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum, tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_smul, TensorProduct.tmul_smul]
  exact Module.Projective.of_split i s hsi

end GlobalTheory
