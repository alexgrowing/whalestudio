import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem lTensor_transl_comul (n : ℕ) (x : G.A (n + 1)) :
    (G.transl n).toLinearMap.lTensor (G.A (n + 1)) (comul (R := R) x) =
      TensorProduct.assoc R _ _ _ ((comul (R := R)).rTensor (G.A 1) (G.transl n x)) := by
  have h1 : (G.transl n).toLinearMap =
      (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ ∘ₗ comul :=
    LinearMap.ext fun a => G.transl_apply n a
  have h2 : ∀ t : (G.A (n + 1) ⊗[R] G.A (n + 1)) ⊗[R] G.A (n + 1),
      ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _).lTensor _ (TensorProduct.assoc R _ _ _ t) =
        TensorProduct.assoc R _ _ _ ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ t) := by
    intro t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u c =>
      induction u with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul a b => simp
  rw [h1, LinearMap.lTensor_comp_apply, ← coassoc_apply, h2, transl_apply]
  congr 1
  generalize comul (R := R) x = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

theorem lTensor_transl_sub_cobOne (n : ℕ) (x : G.A (n + 1)) (b : G.A 1)
    (h : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  have h1 : ∀ t : G.A (n + 1) ⊗[R] G.A (n + 1), TensorProduct.assoc R _ _ _ (t ⊗ₜ (1 : G.A 1)) =
      ((TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor _ t := fun t => by
    induction t with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  have h2 : comul (R := R) (1 : G.A (n + 1)) = 1 ⊗ₜ 1 := by simp [Algebra.TensorProduct.one_def]
  have h3 : G.transl n 1 = 1 ⊗ₜ 1 := by rw [map_one, Algebra.TensorProduct.one_def]
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply, cobOne_apply]
  simp only [map_sub, lTensor_transl_comul, h, map_add, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, h1, h2, h3, AlgHom.toLinearMap_apply, LinearMap.flip_apply, mk_apply,
    assoc_tmul, tmul_add]
  abel

theorem cobOne_transl_invariant {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (x : G.A (n + 1)) (b : G.A 1) (h : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 ∧
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  have h2 := G.lTensor_transl_sub_cobOne n x b h
  refine ⟨?_, h2⟩
  rw [← (mem_symCocycles.1 (cobOne_mem x)).2, LinearMap.rTensor_comm, h2, map_zero]

end PDivGroup

end GlobalTheory
