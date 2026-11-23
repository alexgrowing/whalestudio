import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLinearTensorModuleDecomposition
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_linear_tensor_module_decomposition : ∀ (A R Λ : Type) [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R] (ι : Λ →+* R),
    Submodule.span A (Set.range ι) = ⊤ → ∀ (c : Λ →+* Λ) (cR : R →ₐ[A] R), (∀ a, cR (ι a) = ι (c a)) →
    (∀ a, c (c a) = a) →
    ∀ (T₁ T₂ T : Type) [AddCommGroup T₁] [Module A T₁] [AddCommGroup T₂] [Module A T₂] [AddCommGroup T] [Module A T]
      (ρ₁ : Λ →+* Module.End A T₁) (ρ₂ : Λ →+* Module.End A T₂) (ρ : Λ →+* Module.End A T)
      (e₁ : LinearMap.BilinForm A T₁) (e₂ : LinearMap.BilinForm A T₂) (e : LinearMap.BilinForm A T),
      Function.Bijective e₁ → Function.Bijective e₂ → Function.Bijective e →
      (∀ a x y, e₁ (ρ₁ a x) y = e₁ x (ρ₁ (c a) y)) → (∀ a x y, e₂ (ρ₂ a x) y = e₂ x (ρ₂ (c a) y)) →
      (∀ a x y, e (ρ a x) y = e x (ρ (c a) y)) →
    ∀ (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (φ₁ : m → (T₁ →ₗ[A] T)) (φ₂ : n → (T₂ →ₗ[A] T)) (g₁ : Matrix m m Λ) (g₂ : Matrix n n Λ),
      (∀ k a x, φ₁ k (ρ₁ a x) = ρ a (φ₁ k x)) → (∀ k a x, φ₂ k (ρ₂ a x) = ρ a (φ₂ k x)) →
      (∀ k l x y, e (φ₁ k x) (φ₁ l y) = e₁ (ρ₁ (g₁ k l) x) y) →
      (∀ k l x y, e (φ₂ k x) (φ₂ l y) = e₂ (ρ₂ (g₂ k l) x) y) →
      (∀ k l x y, e (φ₁ k x) (φ₂ l y) = 0) → (∀ k l x y, e (φ₂ k x) (φ₁ l y) = 0) →
    ∀ (f₁ : (Unit → R) ≃ₗ[A] T₁) (f₂ : (Unit → R) ≃ₗ[A] T₂) (f : (m ⊕ n → R) ≃ₗ[A] T),
      (∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r)) → (∀ a r, f₂ (ι a • r) = ρ₂ a (f₂ r)) →
      (∀ a r, f (ι a • r) = ρ a (f r)) →
    ∀ M : Matrix (m ⊕ n) (m ⊕ n) R, (∀ k, f (M (Sum.inl k)) = φ₁ k (f₁ 1)) →
      (∀ k, f (M (Sum.inr k)) = φ₂ k (f₂ 1)) →
      Associated (M.det * cR M.det) (ι (g₁.det * g₂.det)) := by
  first | exact @GlobalTheory.CMNorm.associated_det_mul_conj | exact GlobalTheory.CMNorm.associated_det_mul_conj | (intros; apply GlobalTheory.CMNorm.associated_det_mul_conj <;> assumption)
