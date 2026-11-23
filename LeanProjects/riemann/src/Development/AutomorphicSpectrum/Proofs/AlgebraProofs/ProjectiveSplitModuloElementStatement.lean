import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectiveSplitModuloElement
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_split_modulo_element : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.split_exact_mod | exact GlobalTheory.CompanionTheory.Ar.HT.split_exact_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.split_exact_mod <;> assumption)
