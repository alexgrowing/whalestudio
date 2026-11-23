import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormClassFiniteOfReducedRatAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionNormClassRemoveRationalFactorStatement
open scoped TensorProduct Classical

namespace GlobalTheory.EtaleCls

theorem classes_mod_rat_norms : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ j : E, IsUnit j → τ j = -j → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  intro E _ _ _ _ τ hτ _j _ _ S
  obtain ⟨A, hA⟩ := GlobalTheory.T.normClassFinite_of_reduced_rat_algebra GlobalTheory.T.exists_finite_classes_modulo_involutionNorms E τ hτ S
  exact ⟨A, GlobalTheory.T.involution_norm_class_remove_rational_factor E τ S A hA⟩

end GlobalTheory.EtaleCls
