import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootEquivMk

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LKCent

open GlobalTheory.LKTorus

theorem baseChange_centralizer (K k B A : Type) [Field K] [Field k] [Algebra K k] [Ring B]
    [Algebra K B] [Ring A] [Algebra K A] (γ : B) (f : A →ₐ[K] B) (hf : Function.Injective f)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k) f) ∧
      ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y ↔
        y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) f) := by
  let ad : B →ₗ[K] B := LinearMap.mulRight K γ - LinearMap.mulLeft K γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id k k) f y = LinearMap.lTensor k f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have had : ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) - ((1 : k) ⊗ₜ[K] γ) * y = LinearMap.lTensor k ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact k hex
  refine ⟨?_, fun y => ?_⟩
  · have h := Module.Flat.lTensor_preserves_injective_linearMap (M := k) f.toLinearMap hf
    intro a b hab
    rw [hmap, hmap] at hab
    exact h hab
  · rw [← sub_eq_zero, had, hex' y]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hmap z⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, (hmap z).symm⟩

end GlobalTheory.LKCent

namespace GlobalTheory.LKCent

open GlobalTheory.LKTorus

end GlobalTheory.LKCent

namespace GlobalTheory.LKCent

open GlobalTheory.LKTorus

end GlobalTheory.LKCent
