import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_minors_proportional : ∀ {K : Type} [Field K] {p q : ℕ} (α : Matrix (Fin p) (Fin p ⊕ Fin q) K) (β : Matrix (Fin q) (Fin p ⊕ Fin q) K),
  α * β.transpose = 0 →
  (∃ π₀ : Equiv.Perm (Fin p ⊕ Fin q), (α.submatrix id (π₀ ∘ Sum.inl)).det ≠ 0) →
  (∃ π₁ : Equiv.Perm (Fin p ⊕ Fin q), (β.submatrix id (π₁ ∘ Sum.inr)).det ≠ 0) →
  ∃ lam : K, ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
    ((Equiv.Perm.sign π : ℤ) : K) * (α.submatrix id (π ∘ Sum.inl)).det = lam * (β.submatrix id (π ∘ Sum.inr)).det := by
  first | exact @GlobalTheory.jacobi_complementary_minors | exact GlobalTheory.jacobi_complementary_minors | (intros; apply GlobalTheory.jacobi_complementary_minors <;> assumption)
