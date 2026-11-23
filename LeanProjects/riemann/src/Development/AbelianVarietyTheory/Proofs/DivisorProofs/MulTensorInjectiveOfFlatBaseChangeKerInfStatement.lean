import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInf
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B] [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂), Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ → RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ → a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := by
  first | exact @GlobalTheory.TorStep.mul_tensor_injective | exact GlobalTheory.TorStep.mul_tensor_injective | (intros; apply GlobalTheory.TorStep.mul_tensor_injective <;> assumption)
