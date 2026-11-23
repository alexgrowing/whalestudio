import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariantStatement

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem exists_tensor_map_eq_of_exact {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R M]
    [Module.Flat R N] [Module.Flat R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (h : Function.Exact f g) (F : N ⊗[R] N)
    (h₁ : g.rTensor N F = 0) (h₂ : g.lTensor N F = 0) :
    ∃ c : M ⊗[R] M, TensorProduct.map f f c = F := by
  obtain ⟨F', rfl⟩ := (Module.Flat.lTensor_exact N h F).1 h₂
  have h₃ : g.rTensor M F' = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := P) f hf
    rw [map_zero, ← h₁, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  obtain ⟨c, rfl⟩ := (Module.Flat.rTensor_exact M h F').1 h₃
  exact ⟨c, by rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]⟩

theorem PDivGroup.exists_tensorSquare_mulP_eq {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1))
    (h₁ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0)
    (h₂ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0) :
    ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by
  refine exists_tensor_map_eq_of_exact (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) _
    (Test.mulP_injective G n) (fun a => ⟨fun ha => ?_, ?_⟩) F h₁ h₂
  · exact GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n a (sub_eq_zero.1 ha)
  · rintro ⟨e, rfl⟩
    exact sub_eq_zero.2 (G.transl_mulP n e)

end GlobalTheory
