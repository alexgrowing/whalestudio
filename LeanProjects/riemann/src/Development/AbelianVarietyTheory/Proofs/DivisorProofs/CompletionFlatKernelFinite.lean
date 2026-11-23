import Mathlib
open TensorProduct

namespace GlobalTheory

theorem adicCompletion_tensor_ker_finite : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Flat A M →
  Module.Projective (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) →
  ∀ (n : ℕ) (π : (Fin n → A) →ₗ[A] M), Function.Surjective π →
  Module.Finite (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) (LinearMap.ker π)) := by
  intro A _ f M _ _ hflat hproj n π hπ
  set B := AdicCompletion (Ideal.span {f}) A
  let φ : B ⊗[A] (Fin n → A) →ₗ[B] B ⊗[A] M := AlgebraTensorModule.lTensor B B π
  let ψ : B ⊗[A] (LinearMap.ker π) →ₗ[B] B ⊗[A] (Fin n → A) :=
    AlgebraTensorModule.lTensor B B (LinearMap.ker π).subtype
  have hexact : Function.Exact (LinearMap.ker π).subtype π := by
    intro x; simp
  have hψinj : Function.Injective ψ :=
    LinearMap.lTensor_injective_of_exact_of_flat π hπ _ (LinearMap.ker π).injective_subtype hexact B
  have hψex : Function.Exact ψ φ := lTensor_exact B hexact hπ
  have hφsurj : Function.Surjective φ := LinearMap.lTensor_surjective B hπ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ LinearMap.id hφsurj
  let p : B ⊗[A] (Fin n → A) →ₗ[B] B ⊗[A] (Fin n → A) := LinearMap.id - s ∘ₗ φ
  have hp : ∀ x, p x ∈ LinearMap.ker φ := by
    intro x
    have := LinearMap.congr_fun hs (φ x)
    simp only [LinearMap.mem_ker, p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  have hker : Module.Finite B (LinearMap.ker φ) := by
    refine Module.Finite.of_surjective (p.codRestrict (LinearMap.ker φ) hp) ?_
    rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    ext
    simp only [LinearMap.codRestrict_apply, p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [LinearMap.mem_ker.mp hy, map_zero, sub_zero]
  have hrange : LinearMap.range ψ = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hψex y).symm
  let e : B ⊗[A] (LinearMap.ker π) ≃ₗ[B] LinearMap.ker φ :=
    (LinearEquiv.ofInjective ψ hψinj).trans (LinearEquiv.ofEq _ _ hrange)
  exact Module.Finite.equiv e.symm

end GlobalTheory
