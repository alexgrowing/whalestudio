import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumNondegenerateFiniteHermitianModule
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussSum_nondegenerate_finite_hermitian_module : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  first | exact @GlobalTheory.HermitianGauss.gauss_hermitian | exact GlobalTheory.HermitianGauss.gauss_hermitian | (intros; apply GlobalTheory.HermitianGauss.gauss_hermitian <;> assumption)
