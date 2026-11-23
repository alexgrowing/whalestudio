import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisQuotientTensorBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_quotient_tensor_base_change : ∀ (A B C R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J : Ideal (C ⊗[A] B)) (ψ : C →ₐ[A] R), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k))) = ⊤ := by
  first | (exact @GlobalTheory.quotient_basis_baseChange) | (exact GlobalTheory.quotient_basis_baseChange) | (intros; apply GlobalTheory.quotient_basis_baseChange  <;> assumption)
