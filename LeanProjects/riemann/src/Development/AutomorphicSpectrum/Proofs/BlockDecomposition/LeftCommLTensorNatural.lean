import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiBc

theorem leftComm_lTensor_natural {A B C M N : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup C] [Module A C] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (d : M →ₗ[A] N) (c : C) (w : B ⊗[A] M) :
    (d.lTensor C).lTensor B (TensorProduct.leftComm A C B M (c ⊗ₜ[A] w)) =
      TensorProduct.leftComm A C B N (c ⊗ₜ[A] (d.lTensor B w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [TensorProduct.leftComm_tmul]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem contraction_lTensor :
    ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (C : Type) [AddCommGroup C] [Module A C] (K : ℕ → Type) [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → ∃ H₁ : ∀ n, C ⊗[A] K (n + 1) →ₗ[A] B ⊗[A] (C ⊗[A] K n), (∀ z, H₁ 0 ((d 0).lTensor C z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, ((d n).lTensor C).lTensor B (H₁ n z) + H₁ (n + 1) ((d (n + 1)).lTensor C z) = (1 : B) ⊗ₜ[A] z := by
  intro A _ B _ _ C _ _ K _ _ d H ⟨h0, hS⟩
  refine ⟨fun n => (TensorProduct.leftComm A C B (K n)).toLinearMap ∘ₗ (H n).lTensor C, ?_, ?_⟩
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      simp [h0, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add, hx, hy, TensorProduct.tmul_add]
  · intro n z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c k =>
      have key := congrArg (fun t => TensorProduct.leftComm A C B (K (n + 1)) (c ⊗ₜ[A] t)) (hS n k)
      simp only [TensorProduct.tmul_add, map_add] at key
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul]
      rw [leftComm_lTensor_natural, key, TensorProduct.leftComm_tmul]
    | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add]
      rw [← hx, ← hy]
      abel

end GlobalTheory.CompanionTheory.Dblock.AmiBc
